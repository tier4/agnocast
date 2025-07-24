#pragma once

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/agnocast_tracepoint_wrapper.h"
#include "agnocast/agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <cstdint>
#include <cstring>
#include <mutex>
#include <queue>
#include <thread>

namespace agnocast
{

// These are cut out of the class for information hiding.
topic_local_id_t initialize_publisher(
  const std::string & topic_name, const std::string & node_name, const rclcpp::QoS & qos);
union ioctl_publish_msg_args publish_core(
  [[maybe_unused]] const void * publisher_handle, /* for CARET */ const std::string & topic_name,
  const topic_local_id_t publisher_id, const uint64_t msg_virtual_address,
  std::unordered_map<topic_local_id_t, std::tuple<mqd_t, bool>> & opened_mqs);
uint32_t get_subscription_count_core(const std::string & topic_name);
void increment_borrowed_publisher_num();
void decrement_borrowed_publisher_num();

extern int agnocast_fd;
extern "C" uint32_t agnocast_get_borrowed_publisher_num();

struct PublisherOptions
{
  // For transient local. If true, publish() does both Agnocast publish and ROS 2 publish,
  // regardless of the existence of ROS 2 subscriptions.
  bool do_always_ros2_publish = true;
  // No overrides allowed by default.
  rclcpp::QosOverridingOptions qos_overriding_options;
};

template <typename MessageT>
class Publisher
{
  topic_local_id_t id_ = -1;
  std::string topic_name_;
  std::unordered_map<topic_local_id_t, std::tuple<mqd_t, bool>> opened_mqs_;
  PublisherOptions options_;

  // ROS2 publish related variables
  typename rclcpp::Publisher<MessageT>::SharedPtr ros2_publisher_;
  mqd_t ros2_publish_mq_;
  std::string ros2_publish_mq_name_;
  std::queue<ipc_shared_ptr<MessageT>> ros2_message_queue_;
  std::thread ros2_publish_thread_;
  std::mutex ros2_publish_mtx_;

public:
  using SharedPtr = std::shared_ptr<Publisher<MessageT>>;

  Publisher(
    rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
    const PublisherOptions & options)
  : topic_name_(node->get_node_topics_interface()->resolve_topic_name(topic_name))
  {
    rclcpp::PublisherOptions pub_options;
    pub_options.qos_overriding_options = options.qos_overriding_options;
    ros2_publisher_ = node->create_publisher<MessageT>(topic_name_, qos, pub_options);

    auto actual_qos = ros2_publisher_->get_actual_qos();
    TRACEPOINT(
      agnocast_publisher_init, static_cast<const void *>(this),
      static_cast<const void *>(
        node->get_node_base_interface()->get_shared_rcl_node_handle().get()),
      topic_name_.c_str(), actual_qos.depth());

    if (actual_qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
      options_.do_always_ros2_publish = options.do_always_ros2_publish;
    } else {
      options_.do_always_ros2_publish = false;
    }

    id_ = initialize_publisher(topic_name_, node->get_fully_qualified_name(), actual_qos);

    ros2_publish_mq_name_ = create_mq_name_for_ros2_publish(topic_name_, id_);

    const int mq_mode = 0666;
    struct mq_attr attr = {};
    attr.mq_flags = 0;
    attr.mq_maxmsg = 1;
    attr.mq_msgsize = sizeof(MqMsgROS2Publish);
    attr.mq_curmsgs = 0;
    ros2_publish_mq_ =
      mq_open(ros2_publish_mq_name_.c_str(), O_CREAT | O_WRONLY | O_NONBLOCK, mq_mode, &attr);
    if (ros2_publish_mq_ == -1) {
      RCLCPP_ERROR(logger, "mq_open failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    ros2_publish_thread_ = std::thread([this]() { do_ros2_publish(); });
  }

  ~Publisher()
  {
    MqMsgROS2Publish mq_msg = {};
    mq_msg.should_terminate = true;
    if (mq_send(ros2_publish_mq_, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), 0) == -1) {
      RCLCPP_ERROR(logger, "mq_send failed: %s", strerror(errno));
    }

    ros2_publish_thread_.join();

    if (mq_close(ros2_publish_mq_) == -1) {
      RCLCPP_ERROR(logger, "mq_close failed: %s", strerror(errno));
    }

    if (mq_unlink(ros2_publish_mq_name_.c_str()) == -1) {
      RCLCPP_ERROR(logger, "mq_unlink failed: %s", strerror(errno));
    }
  }

  void do_ros2_publish()
  {
    mqd_t mq = mq_open(ros2_publish_mq_name_.c_str(), O_RDONLY);
    if (mq == -1) {
      RCLCPP_ERROR(logger, "mq_open failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    while (true) {
      MqMsgROS2Publish mq_msg = {};
      auto ret = mq_receive(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), nullptr);
      if (ret == -1) {
        RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      if (mq_msg.should_terminate) {
        break;
      }

      while (true) {
        ipc_shared_ptr<MessageT> message;

        {
          std::scoped_lock lock(ros2_publish_mtx_);
          if (ros2_message_queue_.empty()) {
            break;
          }

          message = std::move(ros2_message_queue_.front());
          ros2_message_queue_.pop();
        }

        ros2_publisher_->publish(*message.get());
      }
    }

    if (mq_close(mq) == -1) {
      RCLCPP_ERROR(logger, "mq_close failed: %s", strerror(errno));
    }
  }

  ipc_shared_ptr<MessageT> borrow_loaned_message()
  {
    increment_borrowed_publisher_num();
    MessageT * ptr = new MessageT();
    return ipc_shared_ptr<MessageT>(ptr, topic_name_.c_str(), id_);
  }

  void publish(ipc_shared_ptr<MessageT> && message)
  {
    if (!message || topic_name_ != message.get_topic_name()) {
      RCLCPP_ERROR(logger, "Invalid message to publish.");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    decrement_borrowed_publisher_num();

    const union ioctl_publish_msg_args publish_msg_args =
      publish_core(this, topic_name_, id_, reinterpret_cast<uint64_t>(message.get()), opened_mqs_);

    message.set_entry_id(publish_msg_args.ret_entry_id);

    for (uint32_t i = 0; i < publish_msg_args.ret_released_num; i++) {
      MessageT * release_ptr = reinterpret_cast<MessageT *>(publish_msg_args.ret_released_addrs[i]);
      delete release_ptr;
    }

    if (options_.do_always_ros2_publish || ros2_publisher_->get_subscription_count() > 0) {
      {
        std::lock_guard<std::mutex> lock(ros2_publish_mtx_);
        ros2_message_queue_.push(std::move(message));
      }

      MqMsgROS2Publish mq_msg = {};
      mq_msg.should_terminate = false;
      if (mq_send(ros2_publish_mq_, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), 0) == -1) {
        // If it returns EAGAIN, it means mq_send has already been executed, but the ros2 publish
        // thread hasn't received it yet. Thus, there's no need to send it again since the
        // notification has already been sent.
        if (errno != EAGAIN) {
          RCLCPP_ERROR(logger, "mq_send failed: %s", strerror(errno));
        }
      }
    } else {
      message.reset();
    }
  }

  uint32_t get_subscription_count() const
  {
    return ros2_publisher_->get_subscription_count() + get_subscription_count_core(topic_name_);
  }
};

}  // namespace agnocast

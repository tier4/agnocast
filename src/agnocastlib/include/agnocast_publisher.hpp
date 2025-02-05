#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"
#include "tracetools/tracetools.h"

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

namespace agnocast
{

// These are cut out of the class for information hiding.
topic_local_id_t initialize_publisher(const pid_t publisher_pid, const std::string & topic_name);
union ioctl_publish_args publish_core(
  const std::string & topic_name, const topic_local_id_t publisher_id, const uint32_t qos_depth,
  const uint64_t msg_virtual_address, std::unordered_map<std::string, mqd_t> & opened_mqs);
uint32_t get_subscription_count_core(const std::string & topic_name);
void increment_borrowed_publisher_num();
void decrement_borrowed_publisher_num();

extern int agnocast_fd;
extern "C" uint32_t get_borrowed_publisher_num();

template <typename MessageT>
class Publisher
{
  topic_local_id_t id_ = -1;
  std::string topic_name_;
  pid_t publisher_pid_;
  rclcpp::QoS qos_;
  // TODO(Koichi98): The mq should be closed when a subscriber unsubscribes the topic, but this is
  // not currently implemented.
  std::unordered_map<std::string, mqd_t> opened_mqs_;
  bool do_always_ros2_publish_;  // For transient local.
  typename rclcpp::Publisher<MessageT>::SharedPtr ros2_publisher_;

public:
  using SharedPtr = std::shared_ptr<Publisher<MessageT>>;

  Publisher(
    rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
    const bool do_always_ros2_publish)
  : topic_name_(node->get_node_topics_interface()->resolve_topic_name(topic_name)),
    publisher_pid_(getpid()),
    qos_(qos),
    ros2_publisher_(node->create_publisher<MessageT>(topic_name_, qos))
  {
#ifdef TRACETOOLS_LTTNG_ENABLED
    TRACEPOINT(
      agnocast_publisher_init, static_cast<const void *>(this),
      static_cast<const void *>(
        node->get_node_base_interface()->get_shared_rcl_node_handle().get()),
      topic_name.c_str(), qos.depth());
#endif

    if (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
      do_always_ros2_publish_ = do_always_ros2_publish;
    } else {
      do_always_ros2_publish_ = false;
    }

    id_ = initialize_publisher(publisher_pid_, topic_name_);
  }

  ipc_shared_ptr<MessageT> borrow_loaned_message()
  {
    increment_borrowed_publisher_num();
    MessageT * ptr = new MessageT();
    return ipc_shared_ptr<MessageT>(ptr, topic_name_.c_str());
  }

  void publish(ipc_shared_ptr<MessageT> && message)
  {
    decrement_borrowed_publisher_num();

    if (!message || topic_name_ != message.get_topic_name()) {
      RCLCPP_ERROR(logger, "Invalid message to publish.");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    const union ioctl_publish_args publish_args = publish_core(
      topic_name_, id_, static_cast<uint32_t>(qos_.depth()),
      reinterpret_cast<uint64_t>(message.get()), opened_mqs_);

#ifdef TRACETOOLS_LTTNG_ENABLED
    TRACEPOINT(
      agnocast_publish, static_cast<const void *>(this), static_cast<const void *>(message.get()),
      publish_args.ret_entry_id);
#endif

    for (uint32_t i = 0; i < publish_args.ret_released_num; i++) {
      MessageT * release_ptr = reinterpret_cast<MessageT *>(publish_args.ret_released_addrs[i]);
      delete release_ptr;
    }

    if (do_always_ros2_publish_ || ros2_publisher_->get_subscription_count() > 0) {
      const MessageT * raw = message.get();
      ros2_publisher_->publish(*raw);
    }

    message.reset();
  }

  uint32_t get_subscription_count() const
  {
    return ros2_publisher_->get_subscription_count() + get_subscription_count_core(topic_name_);
  }
};

}  // namespace agnocast

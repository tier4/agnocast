#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstdint>
#include <cstring>

// These are cut out of the class for information hiding.
uint32_t initialize_publisher(const uint32_t publisher_pid, const std::string & topic_name);
void publish_core(
  const std::string & topic_name, const uint32_t publisher_index, const uint64_t timestamp,
  std::unordered_map<std::string, mqd_t> & opened_mqs);
uint32_t get_subscription_count_core(const std::string & topic_name);
std::vector<uint64_t> borrow_loaned_message_core(
  const std::string & topic_name, const uint32_t publisher_index, const uint32_t qos_depth,
  const uint64_t msg_virtual_address, const uint64_t timestamp);
void increment_borrowed_publisher_num();
void decrement_borrowed_publisher_num();

namespace agnocast
{

extern int agnocast_fd;
extern "C" uint32_t get_borrowed_publisher_num();

template <typename MessageT>
class Publisher
{
  uint32_t index_;
  std::string topic_name_;
  uint32_t publisher_pid_;
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
    if (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
      do_always_ros2_publish_ = do_always_ros2_publish;
    } else {
      do_always_ros2_publish_ = false;
    }

    index_ = initialize_publisher(publisher_pid_, topic_name_);
  }

  ipc_shared_ptr<MessageT> borrow_loaned_message()
  {
    increment_borrowed_publisher_num();
    MessageT * ptr = new MessageT();
    return borrow_loaned_message(ptr);
  }

  ipc_shared_ptr<MessageT> borrow_loaned_message(MessageT * ptr)
  {
    uint64_t timestamp = agnocast_get_timestamp();
    std::vector<uint64_t> released_addrs = borrow_loaned_message_core(
      topic_name_, index_, static_cast<uint32_t>(qos_.depth()), reinterpret_cast<uint64_t>(ptr),
      timestamp);

    for (uint64_t addr : released_addrs) {
      MessageT * release_ptr = reinterpret_cast<MessageT *>(addr);
      delete release_ptr;
    }

    return ipc_shared_ptr<MessageT>(ptr, topic_name_.c_str(), index_, timestamp);
  }

  void publish(ipc_shared_ptr<MessageT> && message)
  {
    if (!message || topic_name_ != message.get_topic_name()) {
      RCLCPP_ERROR(logger, "Invalid message to publish.");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    publish_core(topic_name_, publisher_pid_, message.get_timestamp(), opened_mqs_);
    // We need to decrement borrowed_publisher_num before ros2_publish, otherwise the buffers used
    // for ROS2 serialization will also use shared memory. Since we don't need to store any
    // additional data in shared memory after the agnocast publish operation, here is the ideal
    // point to decrement.
    decrement_borrowed_publisher_num();

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

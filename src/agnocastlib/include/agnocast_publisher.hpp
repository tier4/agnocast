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
void initialize_publisher(uint32_t publisher_pid, const std::string & topic_name);
void publish_core(
  const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp,
  std::unordered_map<std::string, mqd_t> & opened_mqs);
uint32_t get_subscription_count_core(const std::string & topic_name);
std::vector<uint64_t> borrow_loaned_message_core(
  const std::string & topic_name, uint32_t publisher_pid, uint32_t qos_depth,
  uint64_t msg_virtual_address, uint64_t timestamp);

namespace agnocast
{

extern int agnocast_fd;

template <typename MessageT>
class Publisher
{
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

    initialize_publisher(publisher_pid_, topic_name_);
  }

  ipc_shared_ptr<MessageT> borrow_loaned_message()
  {
    MessageT * ptr = new MessageT();
    return borrow_loaned_message(ptr);
  }

  ipc_shared_ptr<MessageT> borrow_loaned_message(MessageT * ptr)
  {
    uint64_t timestamp = agnocast_get_timestamp();
    std::vector<uint64_t> released_addrs = borrow_loaned_message_core(
      topic_name_, publisher_pid_, static_cast<uint32_t>(qos_.depth()),
      reinterpret_cast<uint64_t>(ptr), timestamp);

    for (uint64_t addr : released_addrs) {
      MessageT * release_ptr = reinterpret_cast<MessageT *>(addr);
      delete release_ptr;
    }

    return ipc_shared_ptr<MessageT>(ptr, topic_name_.c_str(), publisher_pid_, timestamp, false);
  }

  void publish(ipc_shared_ptr<MessageT> && message)
  {
    if (!message || topic_name_ != message.get_topic_name()) {
      RCLCPP_ERROR(logger, "Invalid message to publish.");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (do_always_ros2_publish_ || ros2_publisher_->get_subscription_count() > 0) {
      const MessageT * raw = message.get();
      ros2_publisher_->publish(*raw);
    }

    publish_core(topic_name_, publisher_pid_, message.get_timestamp(), opened_mqs_);
    message.reset();
  }

  uint32_t get_subscription_count() const
  {
    return ros2_publisher_->get_subscription_count() + get_subscription_count_core(topic_name_);
  }
};

}  // namespace agnocast

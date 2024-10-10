#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_logger.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
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

namespace agnocast
{

extern int agnocast_fd;
uint64_t agnocast_get_timestamp();

// These are cut out of the class for information hiding.
void initialize_publisher(uint32_t publisher_pid, const std::string & topic_name);
void publish_core(const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp);
uint32_t get_subscription_count_core(const std::string & topic_name);

template <typename MessageT>
class Publisher
{
  std::string topic_name_;
  uint32_t publisher_pid_;
  rclcpp::QoS qos_;
  std::unordered_map<std::string, mqd_t>
    opened_mqs;  // TODO: The mq should be closed when a subscriber unsubscribes the topic, but this
                 // is not currently implemented.

public:
  using SharedPtr = std::shared_ptr<Publisher<MessageT>>;

  Publisher(const std::string & topic_name, const rclcpp::QoS & qos)
  : topic_name_(topic_name), publisher_pid_(getpid()), qos_(qos)
  {
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
    union ioctl_enqueue_and_release_args ioctl_args;
    ioctl_args.topic_name = topic_name_.c_str();
    ioctl_args.publisher_pid = publisher_pid_;
    ioctl_args.qos_depth = static_cast<uint32_t>(qos_.depth());
    ioctl_args.msg_virtual_address = reinterpret_cast<uint64_t>(ptr);
    ioctl_args.timestamp = timestamp;
    if (ioctl(agnocast_fd, AGNOCAST_ENQUEUE_AND_RELEASE_CMD, &ioctl_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_ENQUEUE_AND_RELEASE_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    for (size_t i = 0; i < ioctl_args.ret_len; i++) {
      MessageT * release_ptr = reinterpret_cast<MessageT *>(ioctl_args.ret_released_addrs[i]);
      delete release_ptr;
    }

    return ipc_shared_ptr<MessageT>(ptr, topic_name_.c_str(), publisher_pid_, timestamp, false);
  }

  void publish(ipc_shared_ptr<MessageT> && message)
  {
    if (topic_name_.c_str() != message.get_topic_name()) return;  // string comparison?
    if (publisher_pid_ != message.get_publisher_pid()) return;

    publish_core(topic_name_, publisher_pid_, message.get_timestamp());
  }

  uint32_t get_subscription_count() const { return get_subscription_count_core(topic_name_); }
};

}  // namespace agnocast

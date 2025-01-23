#include "agnocast_smart_pointer.hpp"

using namespace agnocast;

void decrement_rc(
  const std::string & topic_name, const uint32_t publisher_index, const uint32_t subscriber_index,
  const uint64_t timestamp)
{
  union ioctl_update_entry_args entry_args = {};
  entry_args.topic_name = topic_name.c_str();
  entry_args.publisher_index = publisher_index;
  entry_args.subscriber_index = subscriber_index;
  entry_args.msg_timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_DECREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void increment_rc_core(
  const std::string & topic_name, const uint32_t publisher_index, const uint32_t subscriber_index,
  const uint64_t timestamp)
{
  union ioctl_update_entry_args entry_args = {};
  entry_args.topic_name = topic_name.c_str();
  entry_args.publisher_index = publisher_index;
  entry_args.subscriber_index = subscriber_index;
  entry_args.msg_timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_INCREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

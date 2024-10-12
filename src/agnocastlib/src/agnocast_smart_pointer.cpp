#include "agnocast_smart_pointer.hpp"

namespace agnocast
{

void decrement_rc(const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp)
{
  union ioctl_update_entry_args entry_args;
  entry_args.topic_name = topic_name.c_str();
  entry_args.subscriber_pid = getpid();
  entry_args.publisher_pid = publisher_pid;
  entry_args.msg_timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_DECREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void increment_rc_core(const std::string & topic_name, uint32_t publisher_pid, uint64_t timestamp)
{
  union ioctl_update_entry_args entry_args;
  entry_args.topic_name = topic_name.c_str();
  entry_args.subscriber_pid = getpid();
  entry_args.publisher_pid = publisher_pid;
  entry_args.msg_timestamp = timestamp;
  if (ioctl(agnocast_fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_INCREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

}  // namespace agnocast

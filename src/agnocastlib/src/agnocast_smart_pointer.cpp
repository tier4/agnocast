#include "agnocast/agnocast_smart_pointer.hpp"

namespace agnocast
{

void decrement_rc(
  std::string & topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id)
{
  topic_name.reserve(TOPIC_NAME_BUFFER_SIZE);

  struct ioctl_update_entry_args entry_args = {};
  entry_args.topic_name = topic_name.c_str();
  entry_args.pubsub_id = pubsub_id;
  entry_args.entry_id = entry_id;
  if (ioctl(agnocast_fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_DECREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void increment_rc(
  std::string & topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id)
{
  topic_name.reserve(TOPIC_NAME_BUFFER_SIZE);

  struct ioctl_update_entry_args entry_args = {};
  entry_args.topic_name = topic_name.c_str();
  entry_args.pubsub_id = pubsub_id;
  entry_args.entry_id = entry_id;
  if (ioctl(agnocast_fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_INCREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

}  // namespace agnocast

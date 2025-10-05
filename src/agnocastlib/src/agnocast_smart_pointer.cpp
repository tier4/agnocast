#include "agnocast/agnocast_smart_pointer.hpp"

namespace agnocast
{

extern "C" uint32_t agnocast_get_ipc_shared_ptr_num()
{
  return ipc_shared_ptr_num;
}

void increment_ipc_shared_ptr_num()
{
  ipc_shared_ptr_num++;
}

void decrement_ipc_shared_ptr_num()
{
  if (ipc_shared_ptr_num == 0) {
    RCLCPP_ERROR(
      logger,
      "The number of publish() called exceeds the number of borrow_loaned_message() called.");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  ipc_shared_ptr_num--;
}

void decrement_rc(
  const std::string & topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id)
{
  struct ioctl_update_entry_args entry_args = {};
  entry_args.topic_name = {topic_name.c_str(), topic_name.size()};
  entry_args.pubsub_id = pubsub_id;
  entry_args.entry_id = entry_id;
  if (ioctl(agnocast_fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_DECREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void increment_rc(
  const std::string & topic_name, const topic_local_id_t pubsub_id, const int64_t entry_id)
{
  struct ioctl_update_entry_args entry_args = {};
  entry_args.topic_name = {topic_name.c_str(), topic_name.size()};
  entry_args.pubsub_id = pubsub_id;
  entry_args.entry_id = entry_id;
  if (ioctl(agnocast_fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_INCREMENT_RC_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

}  // namespace agnocast

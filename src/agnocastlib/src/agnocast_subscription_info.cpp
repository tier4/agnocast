#include "agnocast/agnocast_subscription_info.hpp"

#include "agnocast/agnocast.hpp"

namespace agnocast
{

std::mutex id2_subscription_info_mtx;
const int subscription_map_bkt_cnt = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, SubscriptionInfo> id2_subscription_info(subscription_map_bkt_cnt);
std::atomic<uint32_t> next_subscription_id;

void receive_message(
  [[maybe_unused]] const uint32_t subscription_id,  // for CARET
  [[maybe_unused]] const pid_t my_pid,              // for CARET
  const SubscriptionInfo & subscription_info, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables)
{
  union ioctl_receive_msg_args receive_args = {};
  receive_args.topic_name = {
    subscription_info.topic_name.c_str(), subscription_info.topic_name.size()};
  receive_args.subscriber_id = subscription_info.subscriber_id;

  {
    std::lock_guard<std::mutex> lock(mmap_mtx);

    if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_RECEIVE_MSG_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    // Map the shared memory region with read permissions whenever a new publisher is discovered.
    for (uint32_t i = 0; i < receive_args.ret_pub_shm_info.publisher_num; i++) {
      const pid_t pid = receive_args.ret_pub_shm_info.publisher_pids[i];
      const uint64_t addr = receive_args.ret_pub_shm_info.shm_addrs[i];
      const uint64_t size = receive_args.ret_pub_shm_info.shm_sizes[i];
      map_read_only_area(pid, addr, size);
    }
  }

  // older messages first
  for (int32_t i = static_cast<int32_t>(receive_args.ret_entry_num) - 1; i >= 0; i--) {
    const std::shared_ptr<std::function<void()>> callable =
      std::make_shared<std::function<void()>>([subscription_info, receive_args, i]() {
        auto typed_msg = subscription_info.message_creator(
          reinterpret_cast<void *>(receive_args.ret_entry_addrs[i]), subscription_info.topic_name,
          subscription_info.subscriber_id, receive_args.ret_entry_ids[i]);
        subscription_info.callback(std::move(*typed_msg));
      });

    {
      constexpr uint8_t PID_SHIFT_BITS = 32;
      uint64_t pid_subscription_id =
        (static_cast<uint64_t>(my_pid) << PID_SHIFT_BITS) | subscription_id;
      TRACEPOINT(
        agnocast_create_callable, static_cast<const void *>(callable.get()),
        receive_args.ret_entry_ids[i], pid_subscription_id);
    }

    {
      std::lock_guard<std::mutex> ready_lock{ready_agnocast_executables_mutex};
      ready_agnocast_executables.emplace_back(
        AgnocastExecutable{callable, subscription_info.callback_group});
    }
  }
}

std::vector<std::string> get_agnocast_topics_by_group(
  const rclcpp::CallbackGroup::SharedPtr & group)
{
  std::vector<std::string> topic_names;

  {
    std::lock_guard<std::mutex> lock(id2_subscription_info_mtx);
    for (const auto & [id, subscription_info] : id2_subscription_info) {
      if (subscription_info.callback_group == group) {
        topic_names.push_back(subscription_info.topic_name);
      }
    }
  }

  std::sort(topic_names.begin(), topic_names.end());

  return topic_names;
}

}  // namespace agnocast

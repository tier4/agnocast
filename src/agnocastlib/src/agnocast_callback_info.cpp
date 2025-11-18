#include "agnocast/agnocast_callback_info.hpp"

#include "agnocast/agnocast.hpp"

namespace agnocast
{

std::mutex id2_callback_info_mtx;
const int callback_map_bkt_cnt = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, CallbackInfo> id2_callback_info(callback_map_bkt_cnt);
std::atomic<uint32_t> next_callback_info_id;
std::atomic<bool> need_epoll_updates{false};

void receive_message(
  [[maybe_unused]] const uint32_t callback_info_id,  // for CARET
  [[maybe_unused]] pid_t my_pid,                     // for CAERT
  const CallbackInfo & callback_info, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables)
{
  union ioctl_receive_msg_args receive_args = {};
  receive_args.topic_name = {callback_info.topic_name.c_str(), callback_info.topic_name.size()};
  receive_args.subscriber_id = callback_info.subscriber_id;

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
      std::make_shared<std::function<void()>>([callback_info, receive_args, i]() {
        auto typed_msg = callback_info.message_creator(
          reinterpret_cast<void *>(receive_args.ret_entry_addrs[i]), callback_info.topic_name,
          callback_info.subscriber_id, receive_args.ret_entry_ids[i]);
        callback_info.callback(std::move(*typed_msg));
      });

    {
      constexpr uint8_t PID_SHIFT_BITS = 32;
      uint64_t pid_ciid = (static_cast<uint64_t>(my_pid) << PID_SHIFT_BITS) | callback_info_id;
      TRACEPOINT(
        agnocast_create_callable, static_cast<const void *>(callable.get()),
        receive_args.ret_entry_ids[i], pid_ciid);
    }

    {
      std::lock_guard<std::mutex> ready_lock{ready_agnocast_executables_mutex};
      ready_agnocast_executables.emplace_back(
        AgnocastExecutable{callable, callback_info.callback_group});
    }
  }
}

void wait_and_handle_epoll_event_impl(
  const int epoll_fd, const pid_t my_pid, const int timeout_ms,
  std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables)
{
  struct epoll_event event = {};

  // blocking with timeout
  const int nfds = epoll_wait(epoll_fd, &event, 1 /*maxevents*/, timeout_ms);

  if (nfds == -1) {
    if (errno != EINTR) {  // signal handler interruption is not error
      RCLCPP_ERROR(logger, "epoll_wait failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return;
  }

  // timeout
  if (nfds == 0) {
    return;
  }

  const uint32_t callback_info_id = event.data.u32;
  CallbackInfo callback_info;

  {
    std::lock_guard<std::mutex> lock(id2_callback_info_mtx);

    const auto it = id2_callback_info.find(callback_info_id);
    if (it == id2_callback_info.end()) {
      RCLCPP_ERROR(logger, "Agnocast internal implementation error: callback info cannot be found");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    callback_info = it->second;
  }

  MqMsgAgnocast mq_msg = {};

  // non-blocking
  auto ret =
    mq_receive(callback_info.mqdes, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), nullptr);
  if (ret < 0) {
    if (errno != EAGAIN) {
      RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return;
  }

  agnocast::receive_message(
    callback_info_id, my_pid, callback_info, ready_agnocast_executables_mutex,
    ready_agnocast_executables);
}

}  // namespace agnocast

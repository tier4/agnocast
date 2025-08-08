#include "agnocast/agnocast_executor.hpp"

#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_tracepoint_wrapper.h"
#include "rclcpp/rclcpp.hpp"
#include "sys/epoll.h"

namespace agnocast
{

AgnocastExecutor::AgnocastExecutor(const rclcpp::ExecutorOptions & options)
: rclcpp::Executor(options), epoll_fd_(epoll_create1(0)), my_pid_(getpid())
{
  if (epoll_fd_ == -1) {
    RCLCPP_ERROR(logger, "epoll_create1 failed: %s", strerror(errno));
    exit(EXIT_FAILURE);
  }
}

AgnocastExecutor::~AgnocastExecutor()
{
  close(epoll_fd_);
}

void AgnocastExecutor::receive_message(
  [[maybe_unused]] const uint32_t callback_info_id,  // for CARET
  const CallbackInfo & callback_info)
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
      uint64_t pid_ciid = (static_cast<uint64_t>(my_pid_) << PID_SHIFT_BITS) | callback_info_id;
      TRACEPOINT(
        agnocast_create_callable, static_cast<const void *>(callable.get()),
        reinterpret_cast<void *>(receive_args.ret_entry_addrs[i]), receive_args.ret_entry_ids[i],
        pid_ciid);
    }

    {
      std::lock_guard ready_lock{ready_agnocast_executables_mutex_};
      ready_agnocast_executables_.emplace_back(
        AgnocastExecutable{callable, callback_info.callback_group});
    }
  }
}

void AgnocastExecutor::prepare_epoll()
{
  std::lock_guard<std::mutex> lock(id2_callback_info_mtx);

  // Check if each callback's callback_group is included in this executor
  for (auto & it : id2_callback_info) {
    const uint32_t callback_info_id = it.first;
    CallbackInfo & callback_info = it.second;
    if (!callback_info.need_epoll_update) {
      continue;
    }

    if (!validate_callback_group(callback_info.callback_group)) {
      continue;
    }

    struct epoll_event ev = {};
    ev.events = EPOLLIN;
    ev.data.u32 = callback_info_id;

    if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, callback_info.mqdes, &ev) == -1) {
      RCLCPP_ERROR(logger, "epoll_ctl failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (callback_info.is_transient_local) {
      receive_message(callback_info_id, callback_info);
    }

    callback_info.need_epoll_update = false;
  }

  const bool all_updated = std::none_of(
    id2_callback_info.begin(), id2_callback_info.end(),
    [](const auto & it) { return it.second.need_epoll_update; });

  if (all_updated) {
    need_epoll_updates.store(false);
  }
}

bool AgnocastExecutor::get_next_agnocast_executable(
  AgnocastExecutable & agnocast_executable, const int timeout_ms)
{
  if (get_next_ready_agnocast_executable(agnocast_executable)) {
    return true;
  }

  wait_and_handle_epoll_event(timeout_ms);

  // Try again
  return get_next_ready_agnocast_executable(agnocast_executable);
}

void AgnocastExecutor::wait_and_handle_epoll_event(const int timeout_ms)
{
  struct epoll_event event = {};

  // blocking with timeout
  const int nfds = epoll_wait(epoll_fd_, &event, 1 /*maxevents*/, timeout_ms);

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

  receive_message(callback_info_id, callback_info);
}

bool AgnocastExecutor::get_next_ready_agnocast_executable(AgnocastExecutable & agnocast_executable)
{
  std::scoped_lock ready_wait_lock{ready_agnocast_executables_mutex_};

  for (auto it = ready_agnocast_executables_.begin(); it != ready_agnocast_executables_.end();
       ++it) {
    // If the executor->add_node() is not called for the node that has this callback_group,
    // get_node_by_group() returns nullptr.
    if (
      rclcpp::Executor::get_node_by_group(
        rclcpp::Executor::weak_groups_to_nodes_, it->callback_group) == nullptr) {
      continue;
    }

    if (
      it->callback_group->type() == rclcpp::CallbackGroupType::MutuallyExclusive &&
      !it->callback_group->can_be_taken_from().exchange(false)) {
      continue;
    }

    agnocast_executable = *it;
    ready_agnocast_executables_.erase(it);

    return true;
  }

  return false;
}

void AgnocastExecutor::execute_agnocast_executable(AgnocastExecutable & agnocast_executable)
{
  TRACEPOINT(
    agnocast_callable_start, static_cast<const void *>(agnocast_executable.callable.get()));
  (*agnocast_executable.callable)();
  TRACEPOINT(agnocast_callable_end, static_cast<const void *>(agnocast_executable.callable.get()));

  if (agnocast_executable.callback_group->type() == rclcpp::CallbackGroupType::MutuallyExclusive) {
    agnocast_executable.callback_group->can_be_taken_from().store(true);
  }
}

}  // namespace agnocast

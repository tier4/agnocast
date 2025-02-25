#include "agnocast_executor.hpp"

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sys/epoll.h"
#include "tracetools/tracetools.h"

namespace agnocast
{

AgnocastExecutor::AgnocastExecutor(
  const rclcpp::ExecutorOptions & options,
  std::chrono::nanoseconds agnocast_callback_group_wait_time)
: rclcpp::Executor(options),
  agnocast_callback_group_wait_time_(agnocast_callback_group_wait_time),
  epoll_fd_(epoll_create1(0)),
  my_pid_(getpid())
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

void AgnocastExecutor::prepare_epoll()
{
  // For added callback groups after calling spin().
  add_callback_groups_from_nodes_associated_to_executor();

  std::lock_guard<std::mutex> lock(id2_callback_info_mtx);
  std::lock_guard<std::mutex> lock2(rclcpp::Executor::mutex_);  // weak_groups_to_nodes_

  // Check if each callback's callback_group is included in this executor
  for (auto & it : id2_callback_info) {
    const uint32_t callback_info_id = it.first;
    CallbackInfo & callback_info = it.second;
    if (!callback_info.need_epoll_update) {
      continue;
    }

    for (const auto & [weak_group, _] : rclcpp::Executor::weak_groups_to_nodes_) {
      const auto group = weak_group.lock();
      if (!group) {
        continue;
      }
      if (group != callback_info.callback_group) {
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

      callback_info.need_epoll_update = false;
      break;
    }
  }
}

bool AgnocastExecutor::get_next_agnocast_executables(
  AgnocastExecutables & agnocast_executables, const int timeout_ms) const
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

    return false;
  }

  // timeout
  if (nfds == 0) {
    return false;
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

    return false;
  }

  union ioctl_receive_msg_args receive_args = {};
  receive_args.topic_name = callback_info.topic_name.c_str();
  receive_args.subscriber_id = callback_info.subscriber_id;
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

  for (int32_t i = static_cast<int32_t>(receive_args.ret_entry_num) - 1; i >= 0;
       i--) {  // older messages first
    const auto callable = agnocast::create_callable(
      reinterpret_cast<void *>(receive_args.ret_entry_addrs[i]), callback_info.subscriber_id,
      receive_args.ret_entry_ids[i], callback_info_id);

#ifdef TRACETOOLS_LTTNG_ENABLED
    uint64_t pid_ciid = (static_cast<uint64_t>(my_pid_) << 32) | callback_info_id;
    TRACEPOINT(
      agnocast_create_callable, static_cast<const void *>(callable.get()),
      reinterpret_cast<void *>(receive_args.ret_entry_addrs[i]), receive_args.ret_entry_ids[i],
      pid_ciid);
#endif

    agnocast_executables.callable_queue.push(callable);
  }

  agnocast_executables.callback_group = callback_info.callback_group;

  return true;
}

void AgnocastExecutor::execute_agnocast_executables(AgnocastExecutables & agnocast_executables)
{
  // In a single-threaded executor, it never sleeps here.
  // For multi-threaded executor, it's workaround to preserve the callback group rule.
  while (!agnocast_executables.callback_group->can_be_taken_from().exchange(false)) {
    std::this_thread::sleep_for(std::chrono::nanoseconds(agnocast_callback_group_wait_time_));
  }

  while (!agnocast_executables.callable_queue.empty()) {
    const auto callable = agnocast_executables.callable_queue.front();
    agnocast_executables.callable_queue.pop();
#ifdef TRACETOOLS_LTTNG_ENABLED
    TRACEPOINT(agnocast_callable_start, static_cast<const void *>(callable.get()));
#endif
    (*callable)();
#ifdef TRACETOOLS_LTTNG_ENABLED
    TRACEPOINT(agnocast_callable_end, static_cast<const void *>(callable.get()));
#endif
  }

  agnocast_executables.callback_group->can_be_taken_from().store(true);
}

void AgnocastExecutor::add_node(rclcpp::Node::SharedPtr node, bool notify)
{
  nodes_.push_back(node);
  Executor::add_node(node, notify);
}

}  // namespace agnocast

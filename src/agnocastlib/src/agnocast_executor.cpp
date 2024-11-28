#include "agnocast_executor.hpp"

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sys/epoll.h"

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
  std::lock_guard<std::mutex> lock(id2_topic_mq_info_mtx);
  std::lock_guard<std::mutex> lock2(rclcpp::Executor::mutex_);  // weak_groups_to_nodes_

  // Check if each callback's callback_group is included in this executor
  for (auto it = id2_topic_mq_info.begin(); it != id2_topic_mq_info.end(); it++) {
    const uint32_t topic_local_id = it->first;
    AgnocastTopicInfo & topic_info = it->second;
    if (!topic_info.need_epoll_update) {
      continue;
    }

    for (const auto & [weak_group, _] : rclcpp::Executor::weak_groups_to_nodes_) {
      const auto group = weak_group.lock();
      if (!group) {
        continue;
      }
      if (group != topic_info.callback_group) {
        continue;
      }

      struct epoll_event ev = {};
      ev.events = EPOLLIN;
      ev.data.u32 = topic_local_id;

      if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, topic_info.mqdes, &ev) == -1) {
        RCLCPP_ERROR(logger, "epoll_ctl failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      topic_info.need_epoll_update = false;
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

  const uint32_t topic_local_id = event.data.u32;
  AgnocastTopicInfo topic_info;

  {
    std::lock_guard<std::mutex> lock(id2_topic_mq_info_mtx);

    const auto it = id2_topic_mq_info.find(topic_local_id);
    if (it == id2_topic_mq_info.end()) {
      RCLCPP_ERROR(logger, "Agnocast internal implementation error: topic info cannot be found");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    topic_info = it->second;
  }

  MqMsgAgnocast mq_msg = {};

  // non-blocking
  auto ret = mq_receive(topic_info.mqdes, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), NULL);
  if (ret < 0) {
    if (errno != EAGAIN) {
      RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return false;
  }

  union ioctl_receive_msg_args receive_args = {};
  receive_args.topic_name = topic_info.topic_name.c_str();
  receive_args.subscriber_pid = my_pid_;
  receive_args.qos_depth = topic_info.qos_depth;

  if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_RECEIVE_MSG_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  for (int32_t i = static_cast<int32_t>(receive_args.ret_len) - 1; i >= 0;
       i--) {  // older messages first
    const auto callable = agnocast::create_callable(
      reinterpret_cast<void *>(receive_args.ret_last_msg_addrs[i]),
      receive_args.ret_publisher_pids[i], receive_args.ret_timestamps[i], topic_local_id);
    agnocast_executables.callable_queue.push(callable);
  }

  agnocast_executables.callback_group = topic_info.callback_group;

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
    (*callable)();
  }

  agnocast_executables.callback_group->can_be_taken_from().store(true);
}

void AgnocastExecutor::add_node(rclcpp::Node::SharedPtr node, bool notify)
{
  nodes_.push_back(node);
  Executor::add_node(node, notify);
}

}  // namespace agnocast

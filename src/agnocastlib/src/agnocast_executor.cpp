#include "agnocast_executor.hpp"

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sys/epoll.h"

namespace agnocast
{

SingleThreadedAgnocastExecutor::SingleThreadedAgnocastExecutor(
  const rclcpp::ExecutorOptions & options)
: rclcpp::Executor(options)
{
  epoll_fd_ = epoll_create1(0);
  if (epoll_fd_ == -1) {
    perror("epoll_create1");
    exit(EXIT_FAILURE);
  }

  my_pid_ = getpid();
}

SingleThreadedAgnocastExecutor::~SingleThreadedAgnocastExecutor()
{
  close(epoll_fd_);
}

void SingleThreadedAgnocastExecutor::spin()
{
  if (spinning.exchange(true)) {
    RCLCPP_ERROR(logger, "spin() called while already spinning");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  RCPPUTILS_SCOPE_EXIT(this->spinning.store(false););

  // TODO: Transient local

  // prepare epoll
  {
    std::lock_guard<std::mutex> lock(id2_topic_mq_info_mtx);

    // Check if each callback's callback_group is included in this executor
    for (auto it = id2_topic_mq_info.begin(); it != id2_topic_mq_info.end(); it++) {
      uint32_t topic_local_id = it->first;
      AgnocastTopicInfo & topic_info = it->second;

      for (auto pair : weak_groups_to_nodes_) {
        auto group = pair.first.lock();
        if (!group) continue;
        if (group != topic_info.callback_group) continue;

        struct epoll_event ev;
        ev.events = EPOLLIN;
        ev.data.u32 = topic_local_id;

        if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, topic_info.mqdes, &ev) == -1) {
          perror("[ERROR] [Agnocast] epoll_ctl failed");
          close(agnocast_fd);
          exit(EXIT_FAILURE);
        }
      }
    }
  }

  while (rclcpp::ok(this->context_) && agnocast::ok() && spinning.load()) {
    agnocast::AgnocastExecutables agnocast_executables;

    if (get_next_agnocast_executables(agnocast_executables, 50 /*ms timed-blocking*/)) {
      execute_agnocast_executables(agnocast_executables);
    }

    rclcpp::AnyExecutable any_executable;
    if (get_next_executable(any_executable, std::chrono::nanoseconds(0) /*non-blocking*/)) {
      execute_any_executable(any_executable);
    }
  }
}

bool SingleThreadedAgnocastExecutor::get_next_agnocast_executables(
  AgnocastExecutables & agnocast_executables, int timeout_ms)
{
  struct epoll_event event;

  // blocking with timeout
  int nfds = epoll_wait(epoll_fd_, &event, 1 /*maxevents*/, timeout_ms);

  if (nfds == -1) {
    if (errno != EINTR) {  // signal handler interruption is not error
      perror("[ERROR] [Agnocast] epoll_wait failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return false;
  }

  // timeout
  if (nfds == 0) return false;

  uint32_t topic_local_id = event.data.u32;
  AgnocastTopicInfo topic_info;

  {
    std::lock_guard<std::mutex> lock(id2_topic_mq_info_mtx);

    auto it = id2_topic_mq_info.find(topic_local_id);
    if (it == id2_topic_mq_info.end()) {
      RCLCPP_ERROR(logger, "Agnocast internal implementation error: topic info cannot be found");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    topic_info = it->second;
  }

  MqMsgAgnocast mq_msg;

  // non-blocking
  auto ret = mq_receive(topic_info.mqdes, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), NULL);
  if (ret < 0) {
    if (errno != EAGAIN) {
      perror("[ERROR] [Agnocast] mq_receive error");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return false;
  }

  union ioctl_receive_msg_args receive_args;
  receive_args.topic_name = topic_info.topic_name.c_str();
  receive_args.subscriber_pid = my_pid_;
  receive_args.qos_depth = topic_info.qos_depth;

  if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_RECEIVE_MSG_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  for (int32_t i = (int32_t)receive_args.ret_len - 1; i >= 0; i--) {  // older messages first
    auto callable = agnocast::create_callable(
      reinterpret_cast<void *>(receive_args.ret_last_msg_addrs[i]),
      receive_args.ret_publisher_pids[i], receive_args.ret_timestamps[i], topic_local_id);
    agnocast_executables.callable_queue.push(callable);
  }

  return true;
}

void SingleThreadedAgnocastExecutor::execute_agnocast_executables(
  AgnocastExecutables & agnocast_executables)
{
  while (!agnocast_executables.callable_queue.empty()) {
    auto callable = agnocast_executables.callable_queue.front();
    agnocast_executables.callable_queue.pop();
    (*callable)();
  }
}

void SingleThreadedAgnocastExecutor::add_node(rclcpp::Node::SharedPtr node, bool notify)
{
  node_ = node;
  Executor::add_node(node, notify);
}

}  // namespace agnocast

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

void SingleThreadedAgnocastExecutor::prepare_epoll()
{
  for (auto it = id2_topic_mq_info.begin(); it != id2_topic_mq_info.end(); it++) {
    AgnocastTopicInfo & topic_info = it->second;

    for (auto pair : weak_groups_to_nodes_) {
      auto group = pair.first.lock();

      if (!group) continue;

      if (group != topic_info.callback_group) continue;

      if (!topic_info.need_epoll_update) continue;
      topic_info.need_epoll_update = false;

      struct epoll_event ev;
      ev.events = EPOLLIN;
      ev.data.u32 = topic_info.topic_local_id;

      if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, topic_info.mqdes, &ev) == -1) {
        perror("epoll_ctl");
        exit(EXIT_FAILURE);
      }
    }
  }
}

void SingleThreadedAgnocastExecutor::spin()
{
  if (spinning.exchange(true)) {
    throw std::runtime_error("spin() called while already spinning");
  }

  RCPPUTILS_SCOPE_EXIT(this->spinning.store(false););

  // TODO: Transient local

  while (rclcpp::ok(this->context_) && agnocast::ok() && spinning.load()) {
    if (need_epoll_updates.exchange(false)) {
      prepare_epoll();
    }

    agnocast::AgnocastExecutable agnocast_executable;
    if (get_next_agnocast_executable(agnocast_executable, 50 /*ms timed-blocking*/)) {
      execute_agnocast_executable(agnocast_executable);
    }

    rclcpp::AnyExecutable any_executable;
    if (get_next_executable(any_executable, std::chrono::nanoseconds(0) /*non-blocking*/)) {
      execute_any_executable(any_executable);
    }
  }
}

bool SingleThreadedAgnocastExecutor::get_next_agnocast_executable(
  AgnocastExecutable & agnocast_executable, int timeout_ms)
{
  struct epoll_event event;

  // blocking with timeout
  int nfds = epoll_wait(epoll_fd_, &event, 1 /*maxevents*/, timeout_ms);
  if (nfds == -1) {
    if (errno != EINTR) perror("epoll_wait");  // signal handler interruption is not error
    return false;
  }

  // timeout
  if (nfds == 0) return false;

  uint32_t topic_local_id = event.data.u32;
  auto it = id2_topic_mq_info.find(topic_local_id);
  if (it == id2_topic_mq_info.end()) {
    throw std::runtime_error("cannot be reached: agnocast topic info cannot be found");
  }

  const AgnocastTopicInfo & topic_info = it->second;
  MqMsgAgnocast mq_msg;

  // non-blocking
  auto ret = mq_receive(topic_info.mqdes, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), NULL);
  if (ret < 0) {
    if (errno != EAGAIN) perror("mq_receive");
    return false;
  }

  union ioctl_receive_msg_args receive_args;
  receive_args.topic_name = topic_info.topic_name;
  receive_args.subscriber_pid = my_pid_;
  receive_args.publisher_pid = mq_msg.publisher_pid;
  receive_args.msg_timestamp = mq_msg.timestamp;
  receive_args.qos_depth = topic_info.qos_depth;
  if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
    perror("AGNOCAST_RECEIVE_MSG_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  if (receive_args.ret == 0) {  // The number of messages > qos_depth
    return false;
  }

  agnocast_executable.callable = agnocast::create_callable(
    reinterpret_cast<void *>(receive_args.ret), topic_info.topic_name, mq_msg.publisher_pid,
    mq_msg.timestamp, true, topic_local_id);

  return true;
}

void SingleThreadedAgnocastExecutor::execute_agnocast_executable(
  const AgnocastExecutable & agnocast_executable)
{
  agnocast_executable.callable();
}

void SingleThreadedAgnocastExecutor::add_node(rclcpp::Node::SharedPtr node, bool notify)
{
  nodes_.push_back(node);
  Executor::add_node(node, notify);
}

}  // namespace agnocast

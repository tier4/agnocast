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
  const uint32_t callback_info_id,  // for CARET
  const CallbackInfo & callback_info)
{
  agnocast::receive_message(
    callback_info_id,  // for CARET
    my_pid_,           // for CARET
    callback_info, ready_agnocast_executables_mutex_, ready_agnocast_executables_);
}

void AgnocastExecutor::prepare_epoll()
{
  agnocast::prepare_epoll_impl(
    epoll_fd_, my_pid_, ready_agnocast_executables_mutex_, ready_agnocast_executables_,
    [this](const rclcpp::CallbackGroup::SharedPtr & group) {
      return validate_callback_group(group);
    });
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

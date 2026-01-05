#include "agnocast/node/agnocast_only_executor.hpp"

#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_callback_info.hpp"
#include "agnocast/agnocast_executor_registry.hpp"
#include "rclcpp/rclcpp.hpp"

#include <memory>
#include <sys/eventfd.h>

namespace agnocast
{

AgnocastOnlyExecutor::AgnocastOnlyExecutor()
: spinning_(false), epoll_fd_(epoll_create1(0)), notify_fd_(-1), my_pid_(getpid())
{
  if (epoll_fd_ == -1) {
    RCLCPP_ERROR(logger, "epoll_create1 failed: %s", strerror(errno));
    exit(EXIT_FAILURE);
  }

  // Create eventfd for receiving notifications about new callbacks/timers
  notify_fd_ = eventfd(0, EFD_NONBLOCK);
  if (notify_fd_ == -1) {
    RCLCPP_ERROR(logger, "eventfd failed: %s", strerror(errno));
    close(epoll_fd_);
    exit(EXIT_FAILURE);
  }

  // Add notify_fd to epoll
  struct epoll_event ev = {};
  ev.events = EPOLLIN;
  ev.data.u32 = NOTIFY_EVENT_FLAG;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, notify_fd_, &ev) == -1) {
    RCLCPP_ERROR(logger, "epoll_ctl failed for notify_fd: %s", strerror(errno));
    close(notify_fd_);
    close(epoll_fd_);
    exit(EXIT_FAILURE);
  }

  // Register this executor's notify_fd to the global registry
  ExecutorRegistry::get_instance().register_executor(notify_fd_);
}

AgnocastOnlyExecutor::~AgnocastOnlyExecutor()
{
  ExecutorRegistry::get_instance().unregister_executor(notify_fd_);
  close(notify_fd_);
  close(epoll_fd_);
}

bool AgnocastOnlyExecutor::get_next_agnocast_executable(
  AgnocastExecutable & agnocast_executable, const int timeout_ms)
{
  if (get_next_ready_agnocast_executable(agnocast_executable)) {
    return true;
  }

  agnocast::wait_and_handle_epoll_event(
    epoll_fd_, notify_fd_, my_pid_, timeout_ms, ready_agnocast_executables_mutex_,
    ready_agnocast_executables_, [this]() {
      agnocast::prepare_epoll_impl(
        epoll_fd_, my_pid_, ready_agnocast_executables_mutex_, ready_agnocast_executables_,
        [](const rclcpp::CallbackGroup::SharedPtr & group) {
          (void)group;
          return true;
        });
    });

  // Try again
  return get_next_ready_agnocast_executable(agnocast_executable);
}

bool AgnocastOnlyExecutor::get_next_ready_agnocast_executable(
  AgnocastExecutable & agnocast_executable)
{
  std::lock_guard<std::mutex> ready_wait_lock{ready_agnocast_executables_mutex_};

  for (auto it = ready_agnocast_executables_.begin(); it != ready_agnocast_executables_.end();
       ++it) {
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

// NOLINTNEXTLINE(readability-convert-member-functions-to-static)
void AgnocastOnlyExecutor::execute_agnocast_executable(AgnocastExecutable & agnocast_executable)
{
  TRACEPOINT(
    agnocast_callable_start, static_cast<const void *>(agnocast_executable.callable.get()));
  (*agnocast_executable.callable)();
  TRACEPOINT(agnocast_callable_end, static_cast<const void *>(agnocast_executable.callable.get()));

  if (agnocast_executable.callback_group->type() == rclcpp::CallbackGroupType::MutuallyExclusive) {
    agnocast_executable.callback_group->can_be_taken_from().store(true);
  }
}

// NOLINTNEXTLINE(readability-convert-member-functions-to-static)
void AgnocastOnlyExecutor::add_node(const std::shared_ptr<agnocast::Node> & node)
{
  (void)node;
}

}  // namespace agnocast

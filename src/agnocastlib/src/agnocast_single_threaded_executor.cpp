#include "agnocast_single_threaded_executor.hpp"

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sys/epoll.h"

namespace agnocast
{

SingleThreadedAgnocastExecutor::SingleThreadedAgnocastExecutor(
  const rclcpp::ExecutorOptions & options, int next_exec_timeout_ms)
: agnocast::AgnocastExecutor(options), next_exec_timeout_ms_(next_exec_timeout_ms)
{
}

void SingleThreadedAgnocastExecutor::spin()
{
  if (spinning.exchange(true)) {
    RCLCPP_ERROR(logger, "spin() called while already spinning");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  RCPPUTILS_SCOPE_EXIT(this->spinning.store(false););

  // TODO(sykwer): Transient local

  while (rclcpp::ok(this->context_) && spinning.load()) {
    if (need_epoll_updates.exchange(false)) {
      prepare_epoll();
    }

    agnocast::AgnocastExecutables agnocast_executables;

    if (get_next_agnocast_executables(
          agnocast_executables, next_exec_timeout_ms_ /*timed-blocking*/)) {
      execute_agnocast_executables(agnocast_executables);
    }

    rclcpp::AnyExecutable any_executable;
    if (get_next_executable(any_executable, std::chrono::nanoseconds(0) /*non-blocking*/)) {
      execute_any_executable(any_executable);
    }
  }
}

}  // namespace agnocast

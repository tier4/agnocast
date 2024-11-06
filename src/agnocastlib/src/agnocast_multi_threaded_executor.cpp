#include "agnocast_multi_threaded_executor.hpp"

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

MultiThreadedAgnocastExecutor::MultiThreadedAgnocastExecutor(
  const rclcpp::ExecutorOptions & options, size_t ros2_number_of_threads,
  size_t agnocast_number_of_threads, bool yield_before_execute,
  std::chrono::nanoseconds next_exec_timeout)
: agnocast::AgnocastExecutor(options),
  yield_before_execute_(yield_before_execute),
  next_exec_timeout_(next_exec_timeout)
{
  if (next_exec_timeout_ == std::chrono::nanoseconds(-1)) {
    RCLCPP_WARN(
      logger,
      "If `next_exec_timeout` is set to infinite, ros2 callbacks which share the callback group "
      "with agnocast callbacks may not be executed. Set this parameter to be short enough");
  }

  ros2_number_of_threads_ =
    ros2_number_of_threads > 0 ? ros2_number_of_threads : std::thread::hardware_concurrency() / 2;
  agnocast_number_of_threads_ = agnocast_number_of_threads > 0
                                  ? agnocast_number_of_threads
                                  : std::thread::hardware_concurrency() / 2;
}

void MultiThreadedAgnocastExecutor::spin()
{
  if (spinning.exchange(true)) {
    RCLCPP_ERROR(logger, "spin() called while already spinning");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  RCPPUTILS_SCOPE_EXIT(this->spinning.store(false););

  // TODO: Transient Local

  std::vector<std::thread> threads;

  {
    std::lock_guard wait_lock{wait_mutex_};

    for (size_t i = 0; i < ros2_number_of_threads_ - 1; i++) {
      auto func = std::bind(&MultiThreadedAgnocastExecutor::ros2_spin, this);
      threads.emplace_back(func);
    }

    for (size_t i = 0; i < agnocast_number_of_threads_; i++) {
      auto func = std::bind(&MultiThreadedAgnocastExecutor::agnocast_spin, this);
      threads.emplace_back(func);
    }
  }

  ros2_spin();

  for (auto & thread : threads) thread.join();
}

void MultiThreadedAgnocastExecutor::ros2_spin()
{
  while (true) {
    rclcpp::AnyExecutable any_executable;

    {
      std::lock_guard wait_lock{wait_mutex_};

      if (!rclcpp::ok(this->context_) || !agnocast::ok()) return;
      if (!get_next_executable(any_executable, next_exec_timeout_)) continue;
    }

    if (yield_before_execute_) std::this_thread::yield();

    execute_any_executable(any_executable);

    // Clear the callback_group to prevent the AnyExecutable destructor from
    // resetting the callback group `can_be_taken_from`.
    // See issue #702 in ros2/rclcpp.
    any_executable.callback_group.reset();
  }
}

void MultiThreadedAgnocastExecutor::agnocast_spin()
{
  while (true) {
    if (need_epoll_updates.exchange(false)) {
      prepare_epoll();
    }

    agnocast::AgnocastExecutables agnocast_executables;

    if (get_next_agnocast_executables(agnocast_executables, 1000 /*ms timed-blocking*/)) {
      if (yield_before_execute_) std::this_thread::yield();

      execute_agnocast_executables(agnocast_executables);
    }
  }
}

}  // namespace agnocast

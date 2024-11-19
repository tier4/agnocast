#include "agnocast_multi_threaded_executor.hpp"

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

MultiThreadedAgnocastExecutor::MultiThreadedAgnocastExecutor(
  const rclcpp::ExecutorOptions & options, size_t number_of_ros2_threads,
  size_t number_of_agnocast_threads, bool ros2_yield_before_execute,
  std::chrono::nanoseconds ros2_next_exec_timeout,
  std::chrono::nanoseconds agnocast_callback_group_wait_time)
: agnocast::AgnocastExecutor(options, agnocast_callback_group_wait_time),
  ros2_yield_before_execute_(ros2_yield_before_execute),
  ros2_next_exec_timeout_(ros2_next_exec_timeout)
{
  if (ros2_next_exec_timeout_ == std::chrono::nanoseconds(-1)) {
    RCLCPP_ERROR(
      logger,
      "If `ros2_next_exec_timeout` is set to infinite, ros2 callbacks which share the callback "
      "group "
      "with agnocast callbacks may not be executed. Set this parameter to be short enough");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  number_of_ros2_threads_ =
    number_of_ros2_threads != 0 ? number_of_ros2_threads : std::thread::hardware_concurrency() / 2;
  number_of_agnocast_threads_ = number_of_agnocast_threads != 0
                                  ? number_of_agnocast_threads
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

  // TODO(sykwer): Transient Local

  std::vector<std::thread> threads;

  {
    std::lock_guard wait_lock{wait_mutex_};

    for (size_t i = 0; i < number_of_ros2_threads_ - 1; i++) {
      auto func = std::bind(&MultiThreadedAgnocastExecutor::ros2_spin, this);
      threads.emplace_back(func);
    }

    for (size_t i = 0; i < number_of_agnocast_threads_; i++) {
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
      if (!get_next_executable(any_executable, ros2_next_exec_timeout_)) continue;
    }

    if (ros2_yield_before_execute_) std::this_thread::yield();

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

    // Unlike a single-threaded executor, in a multi-threaded executor, each thread is dedicated to
    // handling either ROS 2 callbacks or Agnocast callbacks exclusively.
    // Given this separation, get_next_agnocast_executables() can block indefinitely without a
    // timeout. However, since we need to periodically check for epoll updates, we should implement
    // a long timeout period instead of an infinite block.
    if (get_next_agnocast_executables(agnocast_executables, 1000 /*ms timed-blocking*/)) {
      if (ros2_yield_before_execute_) std::this_thread::yield();

      execute_agnocast_executables(agnocast_executables);
    }
  }
}

}  // namespace agnocast

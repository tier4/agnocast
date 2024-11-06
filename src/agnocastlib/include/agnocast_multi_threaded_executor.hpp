#pragma once

#include "agnocast_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <chrono>

namespace agnocast
{

class MultiThreadedAgnocastExecutor : public agnocast::AgnocastExecutor
{
  RCLCPP_DISABLE_COPY(MultiThreadedAgnocastExecutor)

  std::mutex wait_mutex_;
  size_t ros2_number_of_threads_;
  size_t agnocast_number_of_threads_;
  bool yield_before_execute_;
  std::chrono::nanoseconds next_exec_timeout_;

  void ros2_spin();
  void agnocast_spin();

public:
  RCLCPP_PUBLIC
  explicit MultiThreadedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions(),
    size_t ros2_number_of_threads = 0, size_t agnocast_number_of_threads = 0,
    bool yield_before_execute = false,
    std::chrono::nanoseconds next_exec_timeout = std::chrono::nanoseconds(10 * 1000 * 1000));

  RCLCPP_PUBLIC
  void spin() override;
};

}  // namespace agnocast

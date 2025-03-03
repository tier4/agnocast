#pragma once

#include "agnocast/agnocast_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <chrono>

namespace agnocast
{

class MultiThreadedAgnocastExecutor : public agnocast::AgnocastExecutor
{
  RCLCPP_DISABLE_COPY(MultiThreadedAgnocastExecutor)

  std::mutex wait_mutex_;

  /*
  For performance, it is recommented to divide ROS 2's callbacks and Agnocast's callbacks into
  different callback groups. If divided, you can set `ros2_next_exec_timeout` to be long enough
  because we do not have to assume `can_be_taken_from` is changed outside of rclcpp.
  */
  size_t number_of_ros2_threads_;
  size_t number_of_agnocast_threads_;

  bool yield_before_execute_;
  std::chrono::nanoseconds ros2_next_exec_timeout_;
  const int agnocast_next_exec_timeout_ms_;

  void ros2_spin();
  void agnocast_spin();

public:
  RCLCPP_PUBLIC
  explicit MultiThreadedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions(),
    size_t number_of_ros2_threads = 0, size_t number_of_agnocast_threads = 0,
    bool yield_before_execute = false,
    std::chrono::nanoseconds ros2_next_exec_timeout = std::chrono::nanoseconds(10 * 1000 * 1000),
    int agnocast_next_exec_timeout_ms = 1000);

  RCLCPP_PUBLIC
  void spin() override;
};

}  // namespace agnocast

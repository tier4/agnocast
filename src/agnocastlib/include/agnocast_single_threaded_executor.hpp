#pragma once

#include "agnocast_executor.hpp"
#include "agnocast_topic_info.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

class SingleThreadedAgnocastExecutor : public agnocast::AgnocastExecutor
{
  RCLCPP_DISABLE_COPY(SingleThreadedAgnocastExecutor)

  const int next_exec_timeout_ms_;

public:
  RCLCPP_PUBLIC
  explicit SingleThreadedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions(),
    int next_exec_timeout_ms = 50);

  RCLCPP_PUBLIC
  void spin() override;
};

}  // namespace agnocast

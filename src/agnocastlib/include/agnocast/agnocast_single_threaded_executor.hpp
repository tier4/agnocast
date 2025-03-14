#pragma once

#include "agnocast/agnocast_callback_info.hpp"
#include "agnocast/agnocast_executor.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

class SingleThreadedAgnocastExecutor : public agnocast::AgnocastExecutor
{
  RCLCPP_DISABLE_COPY(SingleThreadedAgnocastExecutor)

  const int next_exec_timeout_ms_;
  void validate_callback_group(const rclcpp::CallbackGroup::SharedPtr & group) const override;

public:
  RCLCPP_PUBLIC
  explicit SingleThreadedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions(),
    int next_exec_timeout_ms = 50);

  RCLCPP_PUBLIC
  void spin() override;
};

}  // namespace agnocast

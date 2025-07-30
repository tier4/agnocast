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
  bool validate_callback_group(const rclcpp::CallbackGroup::SharedPtr & group) const override;

  // Activate when this Executor is used for the implementation of a
  // CallbackIsolatedAgnocastExecutor.
  bool is_dedicated_to_one_callback_group_ = false;
  rclcpp::CallbackGroup::SharedPtr dedicated_callback_group_ = nullptr;

public:
  RCLCPP_PUBLIC
  explicit SingleThreadedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions(),
    int next_exec_timeout_ms = 50);

  RCLCPP_PUBLIC
  void spin() override;

  // Not used for public API, but required to be exposed for the internal implementation
  void dedicate_to_callback_group(
    const rclcpp::CallbackGroup::SharedPtr & group,
    const rclcpp::node_interfaces::NodeBaseInterface::SharedPtr & node);
};

}  // namespace agnocast

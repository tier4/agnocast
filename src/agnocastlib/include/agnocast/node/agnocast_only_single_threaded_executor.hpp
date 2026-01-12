#pragma once

#include "agnocast/node/agnocast_only_executor.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

class AgnocastOnlySingleThreadedExecutor : public AgnocastOnlyExecutor
{
  RCLCPP_DISABLE_COPY(AgnocastOnlySingleThreadedExecutor)

  const int next_exec_timeout_ms_;

  // Activate when this Executor is used for the implementation of a
  // AgnocastOnlyCallbackIsolatedExecutor.
  bool is_dedicated_to_one_callback_group_ = false;
  rclcpp::CallbackGroup::SharedPtr dedicated_callback_group_ = nullptr;

public:
  RCLCPP_PUBLIC
  explicit AgnocastOnlySingleThreadedExecutor(int next_exec_timeout_ms = 50);

  RCLCPP_PUBLIC
  void spin() override;

  // Not used for public API, but required to be exposed for the internal implementation
  void dedicate_to_callback_group(
    const rclcpp::CallbackGroup::SharedPtr & group,
    const rclcpp::node_interfaces::NodeBaseInterface::SharedPtr & node);
};

}  // namespace agnocast

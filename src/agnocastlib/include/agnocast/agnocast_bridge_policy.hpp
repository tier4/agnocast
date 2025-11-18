#pragma once

#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, const rclcpp::QoS &)
  {
  }
};
}  // namespace agnocast

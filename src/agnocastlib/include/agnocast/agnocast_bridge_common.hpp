#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const BridgeArgs &);

struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, const rclcpp::QoS &)
  {
  }
};
}  // namespace agnocast

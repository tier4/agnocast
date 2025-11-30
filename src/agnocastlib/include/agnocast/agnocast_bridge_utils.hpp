#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

using BridgeFn = std::shared_ptr<void> (*)(rclcpp::Node::SharedPtr, const BridgeTargetInfo &);

}  // namespace agnocast

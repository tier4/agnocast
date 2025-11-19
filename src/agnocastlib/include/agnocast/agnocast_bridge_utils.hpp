#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

QoSFlat flatten_qos(const rclcpp::QoS & qos);
void safe_strncpy(char * dest, const char * src, size_t dest_size);

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const BridgeArgs &);

}  // namespace agnocast

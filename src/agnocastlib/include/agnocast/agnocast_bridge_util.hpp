#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <mqueue.h>

namespace agnocast
{

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const BridgeArgs &);

QoSFlat flatten_qos(const rclcpp::QoS & qos);
rclcpp::QoS reconstruct_qos(const QoSFlat & q);

void safe_strncpy(char * dest, const char * src, size_t dest_size);

}  // namespace agnocast

#pragma once

#include "agnocast/agnocast_ioctl.hpp"

#include <rclcpp/qos.hpp>

#include <string>
#include <unordered_map>

namespace agnocast
{

enum class FilterMode { ALLOW_ALL, BLACKLIST, WHITELIST };
enum class BridgeDirection { ROS2_TO_AGNOCAST, AGNOCAST_TO_ROS2, BIDIRECTIONAL };

struct BridgeConfig
{
  FilterMode mode = FilterMode::ALLOW_ALL;
  // Key: topic_name, Value: direction
  std::unordered_map<std::string, BridgeDirection> rules;
};

rclcpp::QoS get_subscriber_qos(const std::string & topic_name, topic_local_id_t subscriber_id);
rclcpp::QoS get_publisher_qos(const std::string & topic_name, topic_local_id_t publisher_id);

}  // namespace agnocast

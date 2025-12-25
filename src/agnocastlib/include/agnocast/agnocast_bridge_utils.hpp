#pragma once

#include "agnocast/agnocast_ioctl.hpp"

#include <rclcpp/qos.hpp>

#include <string>
#include <string_view>

namespace agnocast
{
inline constexpr std::string_view SUFFIX_R2A = "_R2A";
inline constexpr std::string_view SUFFIX_A2R = "_A2R";
inline constexpr size_t SUFFIX_LEN = SUFFIX_R2A.length();

enum class BridgeMode { Off, Standard, Performance };
enum class FilterMode { ALLOW_ALL, BLACKLIST, WHITELIST };
enum class BridgeDirection { ROS2_TO_AGNOCAST, AGNOCAST_TO_ROS2, BIDIRECTIONAL };

struct BridgeConfigEntry
{
  std::string topic_name;
  std::string message_type;
  BridgeDirection direction;
};

struct BridgeConfig
{
  std::vector<BridgeConfigEntry> rules;
  FilterMode mode = FilterMode::ALLOW_ALL;
};

BridgeMode get_bridge_mode();
rclcpp::QoS get_subscriber_qos(const std::string & topic_name, topic_local_id_t subscriber_id);
rclcpp::QoS get_publisher_qos(const std::string & topic_name, topic_local_id_t publisher_id);
int get_agnocast_publisher_count(const std::string & topic_name);
int get_agnocast_subscriber_count(const std::string & topic_name);

}  // namespace agnocast

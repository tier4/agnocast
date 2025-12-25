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

enum class BridgeMode : int { Off = 0, Standard = 1, Performance = 2 };

BridgeMode get_bridge_mode();
rclcpp::QoS get_subscriber_qos(const std::string & topic_name, topic_local_id_t subscriber_id);
rclcpp::QoS get_publisher_qos(const std::string & topic_name, topic_local_id_t publisher_id);

}  // namespace agnocast

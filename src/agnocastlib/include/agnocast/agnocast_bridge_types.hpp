#pragma once

#include "rclcpp/rclcpp.hpp"

#include <string>
#include <vector>

namespace agnocast
{
class SubscriptionBase;
}

struct ActiveBridgeR2A
{
  std::string topic_name;
  rclcpp::SubscriptionBase::SharedPtr subscription;
  void * plugin_handle;
};

struct ActiveBridgeA2R
{
  std::string topic_name;
  std::shared_ptr<agnocast::SubscriptionBase> subscription;
  void * plugin_handle;
};

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

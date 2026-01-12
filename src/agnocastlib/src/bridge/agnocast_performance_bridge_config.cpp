#include "agnocast/bridge/agnocast_performance_bridge_config.hpp"

#include "agnocast/bridge/agnocast_bridge_utils.hpp"

#include <rclcpp/rclcpp.hpp>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>

/* Example YAML config file:
filter_mode: "whitelist"
rules:
  bidirectional:
    - /my_topic_1
    - /my_topic_2

  r2a: # ROS2 -> Agnocast
    - /sensor/data
    - /logs

  a2r: # Agnocast -> ROS2
    - /cmd_vel
*/

namespace agnocast
{

PerformanceBridgeConfig::PerformanceBridgeConfig(const rclcpp::Logger & logger) : logger_(logger)
{
  if (!load_config()) {
    RCLCPP_WARN(logger_, "Initialization failed. Using default configuration.");
  }
}

PerformanceBridgeConfig::~PerformanceBridgeConfig() = default;

bool PerformanceBridgeConfig::load_config()
{
  const char * env_path = std::getenv("AGNOCAST_BRIDGE_CONFIG_FILE");
  if (env_path == nullptr) {
    RCLCPP_INFO(logger_, "AGNOCAST_BRIDGE_CONFIG_FILE not set. Mode: ALLOW_ALL.");
    config_ = {};
    return true;
  }

  try {
    YAML::Node root = YAML::LoadFile(env_path);
    BridgeConfig new_config;

    if (auto node = root["filter_mode"]) {
      auto mode = node.as<std::string>();
      std::transform(
        mode.begin(), mode.end(), mode.begin(), [](unsigned char c) { return std::tolower(c); });

      if (mode == "whitelist") {
        new_config.mode = FilterMode::WHITELIST;
      }
      if (mode == "blacklist") {
        new_config.mode = FilterMode::BLACKLIST;
      }
    }

    if (root["rules"]) {
      parse_rules_node(root["rules"], new_config);
    }

    config_ = std::move(new_config);
    return true;
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "Failed to parse '%s': %s. Fallback: ALLOW_ALL.", env_path, e.what());
    config_ = {};
    return false;
  }
}

void PerformanceBridgeConfig::parse_rules_node(
  const YAML::Node & rules_node, BridgeConfig & config_out)
{
  if (!rules_node.IsMap()) {
    RCLCPP_WARN(logger_, "'rules' entry in YAML is not a map. Ignoring rules.");
    return;
  }

  for (const auto & entry : rules_node) {
    auto key = entry.first.as<std::string>();
    std::transform(
      key.begin(), key.end(), key.begin(), [](unsigned char c) { return std::tolower(c); });

    BridgeDirection dir;
    if (key == "r2a") {
      dir = BridgeDirection::ROS2_TO_AGNOCAST;
    } else if (key == "a2r") {
      dir = BridgeDirection::AGNOCAST_TO_ROS2;
    } else if (key == "bidirectional" || key == "bi") {
      dir = BridgeDirection::BIDIRECTIONAL;
    } else {
      continue;
    }

    const auto & topics = entry.second;
    if (!topics.IsSequence()) {
      RCLCPP_WARN(
        logger_, "Topics under '%s' is not a sequence. Ignoring this entry.", key.c_str());
      continue;
    }

    for (const auto & node : topics) {
      config_out.rules[node.as<std::string>()] = dir;
    }
  }
}

bool PerformanceBridgeConfig::is_topic_allowed(
  const std::string & topic_name, BridgeDirection direction) const
{
  // TODO(yutarokobayashi): For debugging. Remove later.
  RCLCPP_INFO(logger_, "Checking topic '%s' for direction %d", topic_name.c_str(), (int)direction);

  if (config_.mode == FilterMode::ALLOW_ALL) {
    return true;
  }

  auto it = config_.rules.find(topic_name);
  bool match_found = false;

  if (it != config_.rules.end()) {
    if (direction_matches(it->second, direction)) {
      match_found = true;
    }
  }

  return (config_.mode == FilterMode::WHITELIST) ? match_found : !match_found;
}

bool PerformanceBridgeConfig::direction_matches(BridgeDirection rule_dir, BridgeDirection req_dir)
{
  if (rule_dir == BridgeDirection::BIDIRECTIONAL) {
    return true;
  }

  return rule_dir == req_dir;
}

BridgeConfig PerformanceBridgeConfig::get_current_config() const
{
  return config_;
}

}  // namespace agnocast

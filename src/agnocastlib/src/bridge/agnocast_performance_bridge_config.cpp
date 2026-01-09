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
  load_config();
}

PerformanceBridgeConfig::~PerformanceBridgeConfig()
{
}

bool PerformanceBridgeConfig::load_config()
{
  BridgeConfig new_config;
  new_config.mode = FilterMode::ALLOW_ALL;
  new_config.rules.clear();

  const char * env_path = std::getenv("AGNOCAST_BRIDGE_CONFIG_FILE");

  if (env_path == nullptr) {
    RCLCPP_INFO(logger_, "AGNOCAST_BRIDGE_CONFIG_FILE is not set. Using default ALLOW_ALL mode.");
    config_ = new_config;
    return true;
  }

  std::string config_path = env_path;
  RCLCPP_INFO(logger_, "Loading bridge config from: %s", config_path.c_str());

  try {
    YAML::Node root = YAML::LoadFile(config_path);

    if (root["filter_mode"]) {
      std::string mode_str = root["filter_mode"].as<std::string>();
      std::transform(mode_str.begin(), mode_str.end(), mode_str.begin(), ::tolower);

      if (mode_str == "whitelist") {
        new_config.mode = FilterMode::WHITELIST;
      } else if (mode_str == "blacklist") {
        new_config.mode = FilterMode::BLACKLIST;
      } else {
        new_config.mode = FilterMode::ALLOW_ALL;
      }
      RCLCPP_INFO(logger_, "Filter Mode set to: %s", mode_str.c_str());
    }

    if (root["rules"]) {
      parse_rules_node(root["rules"], new_config);
      RCLCPP_INFO(logger_, "Loaded %zu filtering rules into map.", new_config.rules.size());
    }

    config_ = new_config;
    return true;

  } catch (const std::exception & e) {
    RCLCPP_ERROR(
      logger_, "Failed to parse config file '%s': %s. Fallback to ALLOW_ALL.", config_path.c_str(),
      e.what());

    config_ = BridgeConfig();
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

  for (YAML::const_iterator dir_it = rules_node.begin(); dir_it != rules_node.end(); ++dir_it) {
    std::string dir_str = dir_it->first.as<std::string>();
    YAML::Node topic_list = dir_it->second;

    BridgeDirection direction;
    std::string dir_str_lower = dir_str;
    std::transform(dir_str_lower.begin(), dir_str_lower.end(), dir_str_lower.begin(), ::tolower);

    if (dir_str_lower == "r2a") {
      direction = BridgeDirection::ROS2_TO_AGNOCAST;
    } else if (dir_str_lower == "a2r") {
      direction = BridgeDirection::AGNOCAST_TO_ROS2;
    } else if (dir_str_lower == "bidirectional" || dir_str_lower == "bi") {
      direction = BridgeDirection::BIDIRECTIONAL;
    } else {
      RCLCPP_WARN(logger_, "Unknown direction key '%s'. Skipping.", dir_str.c_str());
      continue;
    }

    if (!topic_list.IsSequence()) {
      RCLCPP_WARN(logger_, "Topic list for '%s' is not a sequence. Skipping.", dir_str.c_str());
      continue;
    }

    for (const auto & topic_node : topic_list) {
      std::string topic_name = topic_node.as<std::string>();

      if (config_out.rules.find(topic_name) != config_out.rules.end()) {
        RCLCPP_WARN(
          logger_, "Duplicate rule for topic '%s'. Overwriting with direction '%s'.",
          topic_name.c_str(), dir_str.c_str());
      }

      config_out.rules[topic_name] = direction;

      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Rule added: Topic='%s', Dir='%s'", topic_name.c_str(), dir_str.c_str());
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

  if (config_.mode == FilterMode::WHITELIST) {
    if (match_found) {
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Topic '%s' ALLOWED by whitelist.", topic_name.c_str());
      return true;
    } else {
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Topic '%s' DENIED by whitelist.", topic_name.c_str());
      return false;
    }
  } else {
    // BLACKLIST mode
    if (match_found) {
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_WARN(logger_, "Topic '%s' DENIED by blacklist.", topic_name.c_str());
      return false;
    } else {
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Topic '%s' ALLOWED by blacklist.", topic_name.c_str());
      return true;
    }
  }
}

bool PerformanceBridgeConfig::direction_matches(
  BridgeDirection rule_dir, BridgeDirection req_dir) const
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

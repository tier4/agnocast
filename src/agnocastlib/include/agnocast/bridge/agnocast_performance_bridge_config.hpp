#pragma once

#include "agnocast/bridge/agnocast_bridge_utils.hpp"

#include <rclcpp/logger.hpp>

#include <yaml-cpp/yaml.h>

#include <mutex>
#include <string>

namespace agnocast
{

class PerformanceBridgeConfig
{
public:
  explicit PerformanceBridgeConfig(const rclcpp::Logger & logger);
  ~PerformanceBridgeConfig();

  bool load_config();
  bool is_topic_allowed(const std::string & topic_name, BridgeDirection direction) const;
  BridgeConfig get_current_config() const;

private:
  rclcpp::Logger logger_;
  BridgeConfig config_;

  void parse_rules_node(const YAML::Node & rules, BridgeConfig & config_out);
  bool direction_matches(BridgeDirection rule_dir, BridgeDirection req_dir) const;
};

}  // namespace agnocast

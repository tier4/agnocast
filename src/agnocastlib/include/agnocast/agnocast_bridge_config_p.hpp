#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"

#include <rclcpp/logger.hpp>

#include <yaml-cpp/yaml.h>

#include <mutex>
#include <string>
#include <vector>

namespace agnocast
{

class BridgeConfigP
{
public:
  explicit BridgeConfigP(const rclcpp::Logger & logger);
  ~BridgeConfigP();

  /**
   * @brief 環境変数 AGNOCAST_BRIDGE_FILTER_FILE から設定を読み込む
   * @return 読み込みに成功したら true
   */
  bool load_config();

  /**
   * @brief 指定されたトピックと方向が、現在の設定で許可されているか判定する
   */
  bool is_topic_allowed(const std::string & topic_name, BridgeDirection direction) const;

  /**
   * @brief 現在の設定設定を取得（デバッグ用など）
   */
  BridgeConfig get_current_config() const;

private:
  rclcpp::Logger logger_;
  BridgeConfig config_;  // 現在の設定データ

  // ヘルパー関数
  void parse_rules_node(const YAML::Node & rules, BridgeConfig & config_out);
  bool direction_matches(BridgeDirection rule_dir, BridgeDirection req_dir) const;
};

}  // namespace agnocast
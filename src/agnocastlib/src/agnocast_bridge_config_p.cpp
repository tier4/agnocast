#include "agnocast/agnocast_bridge_config_p.hpp"

#include <rclcpp/rclcpp.hpp>

#include <algorithm>  // std::transform
#include <cstdlib>    // std::getenv
#include <fstream>
#include <string>
#include <vector>

namespace agnocast
{

BridgeConfigP::BridgeConfigP(const rclcpp::Logger & logger) : logger_(logger)
{
  // コンストラクタで初期設定をロード
  load_config();
}

BridgeConfigP::~BridgeConfigP()
{
}

bool BridgeConfigP::load_config()
{
  // ★ロック削除 (シングルスレッド動作のため不要)

  // 初期化（デフォルトは全許可）
  BridgeConfig new_config;
  new_config.mode = FilterMode::ALLOW_ALL;

  // 環境変数の取得
  const char * env_path = std::getenv("AGNOCAST_BRIDGE_FILTER_FILE");

  if (env_path == nullptr) {
    RCLCPP_INFO(logger_, "AGNOCAST_BRIDGE_FILTER_FILE is not set. Using default ALLOW_ALL mode.");
    config_ = new_config;
    return true;
  }

  std::string config_path = env_path;
  RCLCPP_INFO(logger_, "Loading bridge config from: %s", config_path.c_str());

  try {
    YAML::Node root = YAML::LoadFile(config_path);

    // 1. filter_mode の読み込み (YAMLキー変更: mode -> filter_mode)
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

    // 2. rules の読み込み (構造変更に対応)
    if (root["rules"]) {
      parse_rules_node(root["rules"], new_config);
      RCLCPP_INFO(logger_, "Loaded %zu filtering rules.", new_config.rules.size());
    }

    // メンバ変数へ適用
    config_ = new_config;
    return true;

  } catch (const std::exception & e) {
    RCLCPP_ERROR(
      logger_, "Failed to parse config file '%s': %s. Fallback to ALLOW_ALL.", config_path.c_str(),
      e.what());

    // エラー時は安全側に倒す
    config_ = BridgeConfig();  // Default: ALLOW_ALL
    return false;
  }
}

// ネストされたYAML構造 (Type -> Direction -> TopicList) をパースする関数
void BridgeConfigP::parse_rules_node(const YAML::Node & rules, BridgeConfig & config_out)
{
  // rules は Map である必要があります
  if (!rules.IsMap()) {
    RCLCPP_WARN(logger_, "'rules' entry in YAML is not a map. Ignoring rules.");
    return;
  }

  // Loop 1: メッセージ型 (Key: Type, Value: DirectionMap)
  for (YAML::const_iterator type_it = rules.begin(); type_it != rules.end(); ++type_it) {
    std::string message_type = type_it->first.as<std::string>();
    YAML::Node dir_map = type_it->second;

    if (!dir_map.IsMap()) {
      RCLCPP_WARN(
        logger_, "Value for type '%s' is not a map (expected directions). Skipping.",
        message_type.c_str());
      continue;
    }

    // Loop 2: 方向 (Key: Direction, Value: TopicList)
    for (YAML::const_iterator dir_it = dir_map.begin(); dir_it != dir_map.end(); ++dir_it) {
      std::string dir_str = dir_it->first.as<std::string>();
      YAML::Node topic_list = dir_it->second;

      // 方向文字列を Enum に変換
      BridgeDirection direction;
      std::string dir_str_lower = dir_str;
      std::transform(dir_str_lower.begin(), dir_str_lower.end(), dir_str_lower.begin(), ::tolower);

      if (dir_str_lower == "r2a") {
        direction = BridgeDirection::ROS2_TO_AGNOCAST;
      } else if (dir_str_lower == "a2r") {
        direction = BridgeDirection::AGNOCAST_TO_ROS2;
      } else {
        // "bidirectional" or others
        direction = BridgeDirection::BIDIRECTIONAL;
      }

      if (!topic_list.IsSequence()) {
        RCLCPP_WARN(
          logger_, "Topic list for '%s' -> '%s' is not a sequence. Skipping.", message_type.c_str(),
          dir_str.c_str());
        continue;
      }

      // Loop 3: トピックリスト (Item: TopicName)
      for (const auto & topic_node : topic_list) {
        BridgeConfigEntry entry;
        entry.topic_name = topic_node.as<std::string>();
        entry.message_type = message_type;  // 型情報も保存しておく
        entry.direction = direction;

        // フラットなリストとして保存
        config_out.rules.push_back(entry);

        // 詳細ログ (DEBUGレベル推奨ですが、INFOご希望とのことでINFOにします)
        RCLCPP_INFO(
          logger_, "Rule added: Topic='%s', Type='%s', Dir='%s'", entry.topic_name.c_str(),
          entry.message_type.c_str(), dir_str.c_str());
      }
    }
  }
}

bool BridgeConfigP::is_topic_allowed(
  const std::string & topic_name, BridgeDirection direction) const
{
  RCLCPP_INFO(
    logger_, "Checking if topic '%s' is allowed for direction %d", topic_name.c_str(),
    (int)direction);

  // ALLOW_ALL なら無条件許可
  if (config_.mode == FilterMode::ALLOW_ALL) {
    // ログを残す
    RCLCPP_INFO(
      logger_, "Filter Mode is ALLOW_ALL. Topic '%s' allowed by default.", topic_name.c_str());
    return true;
  }

  bool match_found = false;
  for (const auto & rule : config_.rules) {
    // トピック名の完全一致
    if (rule.topic_name == topic_name) {
      // 方向の一致確認
      if (direction_matches(rule.direction, direction)) {
        match_found = true;
        break;
      }
    }
  }

  if (config_.mode == FilterMode::WHITELIST) {
    // ホワイトリスト: ルールにあれば許可、なければ拒否
    if (match_found) {
      RCLCPP_INFO(logger_, "Topic '%s' ALLOWED by whitelist.", topic_name.c_str());
      return true;
    } else {
      RCLCPP_WARN(
        logger_, "Topic '%s' DENIED by whitelist (No matching rule).", topic_name.c_str());
      return false;
    }
  } else {
    // ブラックリスト: ルールにあったら拒否、なければ許可
    if (match_found) {
      RCLCPP_WARN(logger_, "Topic '%s' DENIED by blacklist.", topic_name.c_str());
      return false;
    } else {
      RCLCPP_INFO(
        logger_, "Topic '%s' ALLOWED by blacklist (No matching rule).", topic_name.c_str());
      return true;
    }
  }
}

bool BridgeConfigP::direction_matches(BridgeDirection rule_dir, BridgeDirection req_dir) const
{
  if (rule_dir == BridgeDirection::BIDIRECTIONAL) {
    return true;
  }
  return rule_dir == req_dir;
}

BridgeConfig BridgeConfigP::get_current_config() const
{
  // ★ロック削除
  return config_;
}

}  // namespace agnocast

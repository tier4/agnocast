#pragma once

#include <rclcpp/rclcpp.hpp>

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

// API定義をインクルード (これで BridgeEntryR2A などが使えるようになります)
#include "agnocast/agnocast_bridge_plugin_api.hpp"
#include "agnocast/agnocast_utils.hpp"

namespace agnocast
{

class BridgeLoaderP
{
public:
  explicit BridgeLoaderP(const rclcpp::Logger & logger);
  ~BridgeLoaderP();

  // R2A (ROS 2 -> Agnocast) ブリッジ作成
  rclcpp::SubscriptionBase::SharedPtr create_r2a_bridge(
    rclcpp::Node::SharedPtr node, const std::string & topic_name, const std::string & message_type,
    const rclcpp::QoS & qos);

  // A2R (Agnocast -> ROS 2) ブリッジ作成
  std::shared_ptr<agnocast::SubscriptionBase> create_a2r_bridge(
    rclcpp::Node::SharedPtr node, const std::string & topic_name, const std::string & message_type,
    const rclcpp::QoS & qos);

private:
  // 型名をファイル名用形式に変換 (pkg/msg/Type -> pkg_msg_Type)
  std::string convert_type_to_snake_case(const std::string & message_type) const;

  // amentを使ってフルパスのライブラリ名を生成
  std::string generate_library_path(
    const std::string & snake_type, const std::string & plugin_suffix) const;

  // ライブラリをロードまたはキャッシュから取得
  void * load_library(const std::string & library_path);

  rclcpp::Logger logger_;

  // ロード済みライブラリのハンドルキャッシュ (path -> handle)
  std::unordered_map<std::string, void *> loaded_libraries_;
};

}  // namespace agnocast

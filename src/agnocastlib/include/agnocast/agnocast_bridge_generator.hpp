#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <mqueue.h>
#include <sys/types.h>

#include <map>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

namespace agnocast
{

// agnocast_utils.cpp 等で定義されるファイルディスクリプタ
extern int agnocast_fd;

class BridgeGenerator
{
public:
  explicit BridgeGenerator(pid_t target_pid);
  ~BridgeGenerator();

  // コピー・ムーブ禁止
  BridgeGenerator(const BridgeGenerator &) = delete;
  BridgeGenerator & operator=(const BridgeGenerator &) = delete;
  BridgeGenerator(BridgeGenerator &&) = delete;
  BridgeGenerator & operator=(BridgeGenerator &&) = delete;

  void run();

private:
  void setup_mq();
  void setup_signals();
  void setup_epoll();

  void handle_mq_event();
  void handle_signal_event();

  // 作成処理 (委譲された場合もこれを使う)
  void load_and_add_node(const MqMsgBridge & req, const std::string & unique_key);

  // 削除処理
  void remove_bridge_node(const std::string & unique_key);

  const pid_t target_pid_;
  std::string mq_name_;
  rclcpp::Logger logger_;

  mqd_t mq_fd_ = (mqd_t)-1;
  int epoll_fd_ = -1;
  int signal_fd_ = -1;

  bool shutdown_requested_ = false;

  // --- Executor / Node Management ---

  // 全ブリッジの親となるコンテナノード (1プロセス1つ)
  rclcpp::Node::SharedPtr container_node_;

  // Agnocast専用Executor
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;

  std::thread executor_thread_;
  std::mutex executor_mutex_;

  // 動的ロードしたライブラリハンドル (保持してアンロード防止)
  std::vector<std::shared_ptr<void>> dl_handles_;

  // 生成されたブリッジインスタンス (寿命管理用)
  // key: unique_key ("topic_R2A" etc)
  // value: ブリッジのリソース (shared_ptr<void>)
  std::map<std::string, std::shared_ptr<void>> active_bridges_;

  // 参照カウンタ (プロセス内での利用数)
  // key: unique_key
  std::map<std::string, int> bridge_ref_counts_;

  // 関数ポインタキャッシュ (委譲対応用)
  // key: unique_key (これから作られるべきブリッジのキー, 例: "topic_A2R")
  // value: 生成用関数ポインタ
  std::map<std::string, BridgeFn> cached_factories_;
};

}  // namespace agnocast
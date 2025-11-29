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
  // --- Initialization ---
  void setup_mq();
  void setup_signals();
  void setup_epoll();

  // --- Event Handlers ---
  // 親プロセスからの制御コマンド (Control Plane)
  void handle_parent_mq_event();

  // 他Generatorからの委譲/連携コマンド (Delegation Plane)
  void handle_child_mq_event();

  void handle_signal_event();

  // --- Core Logic ---
  // ブリッジ作成・ロード (オーナー権限取得後、または委譲によるリクエストで実行)
  void load_and_add_node(const MqMsgBridge & req, const std::string & unique_key);

  // ブリッジ削除 (参照カウント0時)
  void remove_bridge_node(const std::string & unique_key);

  // 他のGeneratorへ委譲リクエストを送信するヘルパー
  void send_delegate_request(pid_t target_pid, const MqMsgBridge & req);

  // --------------------------------------------------------

  const pid_t target_pid_;
  rclcpp::Logger logger_;

  // MQ Handles
  // 1. Parent MQ: 親プロセス(target_pid_) -> 自分
  mqd_t mq_parent_fd_ = (mqd_t)-1;
  std::string mq_parent_name_;

  // 2. Child MQ: 他のGenerator -> 自分(getpid())
  mqd_t mq_child_fd_ = (mqd_t)-1;
  std::string mq_child_name_;

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
  // NOTE: 委譲した場合(オーナーが他人)、ここには nullptr が入る場合がある
  std::map<std::string, std::shared_ptr<void>> active_bridges_;

  // 参照カウンタ (プロセス内での利用数)
  // key: unique_key
  std::map<std::string, int> bridge_ref_counts_;

  // 関数ポインタキャッシュ (逆方向ブリッジ作成用)
  // key: unique_key (これから作られるべきブリッジのキー, 例: "topic_A2R")
  // value: 生成用関数ポインタ
  std::map<std::string, BridgeFn> cached_factories_;
};

}  // namespace agnocast
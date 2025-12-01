#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <mqueue.h>
#include <sys/epoll.h>
#include <sys/types.h>

#include <map>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

namespace agnocast
{

extern int agnocast_fd;

class BridgeGenerator
{
public:
  explicit BridgeGenerator(pid_t target_pid);
  ~BridgeGenerator();

  BridgeGenerator(const BridgeGenerator &) = delete;
  BridgeGenerator & operator=(const BridgeGenerator &) = delete;
  BridgeGenerator(BridgeGenerator &&) = delete;
  BridgeGenerator & operator=(BridgeGenerator &&) = delete;

  void run();

private:
  void setup_mq();
  void setup_signals();
  void setup_epoll();

  void setup_ros_execution();
  void check_parent_alive();

  void handle_epoll_events(const struct epoll_event * events, int count);
  void handle_mq_event(mqd_t fd, bool allow_delegation);
  void handle_signal_event();

  void create_bridge_safely(const MqMsgBridge & req, const std::string & unique_key);
  void load_and_add_node(const MqMsgBridge & req, const std::string & unique_key);
  void remove_bridge_node(const std::string & unique_key);
  void send_delegate_request(pid_t target_pid, const MqMsgBridge & req);

  // 親プロセス切り離し用
  void check_should_exit();

  void check_connection_demand();

  const pid_t target_pid_;
  rclcpp::Logger logger_;
  bool is_parent_alive_{true};  // 親生存フラグ

  mqd_t mq_parent_fd_ = (mqd_t)-1;
  std::string mq_parent_name_;

  mqd_t mq_child_fd_ = (mqd_t)-1;
  std::string mq_child_name_;

  int epoll_fd_ = -1;
  int signal_fd_ = -1;

  bool shutdown_requested_ = false;

  rclcpp::Node::SharedPtr container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;
  std::mutex executor_mutex_;

  // アクティブなブリッジ (key: unique_key)
  std::map<std::string, std::shared_ptr<void>> active_bridges_;

  // 関数ポインタキャッシュ (ライブラリハンドル保持用)
  // value: pair<関数ポインタ, ライブラリハンドル>
  std::map<std::string, std::pair<BridgeFn, std::shared_ptr<void>>> cached_factories_;
};

}  // namespace agnocast
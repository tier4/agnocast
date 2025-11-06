#pragma once

#include "agnocast/agnocast_bridge_types.hpp"
#include "agnocast/agnocast_mq.hpp"

#include <rclcpp/rclcpp.hpp>

#include <mqueue.h>

#include <atomic>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

namespace agnocast
{

extern int agnocast_fd;

class BridgeManager
{
public:
  BridgeManager();
  ~BridgeManager();
  void run();

private:
  std::vector<ActiveBridgeR2A> active_r2a_bridges_;
  std::vector<ActiveBridgeA2R> active_a2r_bridges_;
  std::vector<std::thread> worker_threads_;
  std::mutex bridge_mutex_;
  BridgeConfig bridge_config_;

  rclcpp::Node::SharedPtr node_;
  rclcpp::Logger logger_;
  std::unique_ptr<rclcpp::Executor> executor_;
  std::thread spin_thread_;

  mqd_t mq_;
  int epoll_fd_;
  std::string mq_name_str_;

  void launch_r2a_bridge_thread(const BridgeRequest & request);
  void launch_a2r_bridge_thread(const BridgeRequest & request);
  void handle_bridge_request();
  void reload_and_update_bridges();

  void check_and_shutdown_idle_bridges();
  void check_and_shutdown_daemon_if_idle();
  void shutdown_manager_internal();

  BridgeConfig parse_bridge_config();
  std::unique_ptr<rclcpp::Executor> select_executor();

  static std::atomic<bool> reload_filter_request_;
  static void sighup_handler(int signum);
};
}  // namespace agnocast
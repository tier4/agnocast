#pragma once

#include "agnocast/agnocast_bridge_config_p.hpp"
#include "agnocast/agnocast_bridge_ipc_event_loop_p.hpp"
#include "agnocast/agnocast_bridge_loader_p.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "agnocast/agnocast_subscription.hpp"

#include <rclcpp/rclcpp.hpp>

#include <atomic>
#include <memory>
#include <string>
#include <thread>
#include <vector>

namespace agnocast
{

class PerformanceBridgeManager
{
public:
  PerformanceBridgeManager();
  ~PerformanceBridgeManager();
  void run();

private:
  // Members
  rclcpp::Logger logger_;
  BridgeIpcEventLoopP event_loop_;
  BridgeLoaderP loader_;

  // ROS Execution
  std::shared_ptr<rclcpp::Node> container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;

  // State
  bool shutdown_requested_ = false;

  std::unordered_map<std::string, rclcpp::SubscriptionBase::SharedPtr> active_r2a_bridges_;
  std::unordered_map<std::string, std::shared_ptr<agnocast::SubscriptionBase>> active_a2r_bridges_;

  std::unique_ptr<BridgeConfigP> config_handler_;

  // Initialization
  void start_ros_execution();

  // Event Callbacks
  void on_mq_request(int fd);
  void on_signal();
  void on_reload();

  // Periodic Checks
  void check_and_request_shutdown();
  void check_and_remove_bridges();
};

}  // namespace agnocast
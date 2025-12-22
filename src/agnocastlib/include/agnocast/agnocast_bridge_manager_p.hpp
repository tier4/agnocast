#pragma once

#include "agnocast/agnocast_bridge_config_p.hpp"
#include "agnocast/agnocast_bridge_ipc_event_loop_p.hpp"
#include "agnocast/agnocast_bridge_loader_p.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"

#include <rclcpp/rclcpp.hpp>

#include <atomic>
#include <memory>
#include <thread>

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
  BridgeConfigP config_;

  // ROS Execution
  std::shared_ptr<rclcpp::Node> container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;

  // State
  std::atomic<bool> shutdown_requested_;

  void start_ros_execution();

  void on_mq_request(int fd);
  void on_signal();
  void on_reload();
};

}  // namespace agnocast
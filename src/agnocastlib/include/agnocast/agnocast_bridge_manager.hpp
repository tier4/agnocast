#pragma once

#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"
#include "agnocast/agnocast_bridge_loader.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <memory>

namespace agnocast
{

class BridgeManager
{
public:
  explicit BridgeManager(pid_t target_pid);
  ~BridgeManager();

  BridgeManager(const BridgeManager &) = delete;
  BridgeManager & operator=(const BridgeManager &) = delete;

  void run();

private:
  const pid_t target_pid_;
  rclcpp::Logger logger_;

  BridgeIpcEventLoop event_loop_;
  BridgeLoader loader_;

  rclcpp::Node::SharedPtr container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;

  void start_ros_execution();
};

}  // namespace agnocast

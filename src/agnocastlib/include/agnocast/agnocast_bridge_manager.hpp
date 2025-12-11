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

  bool is_parent_alive_ = true;
  bool shutdown_requested_ = false;

  rclcpp::Node::SharedPtr container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;

  std::map<std::string, std::shared_ptr<void>> active_bridges_;

  void start_ros_execution();

  void on_mq_event(mqd_t fd, bool allow_delegation);

  void handle_create_request(const MqMsgBridge & req, bool allow_delegation);

  void check_parent_alive();
  void check_active_bridges();
  void check_should_exit();

  void remove_active_bridges(const std::string & topic_name_with_dirction);
};

}  // namespace agnocast

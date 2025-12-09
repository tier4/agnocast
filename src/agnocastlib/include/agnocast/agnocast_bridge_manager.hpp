#pragma once

#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"
#include "agnocast/agnocast_bridge_loader.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <map>
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
  explicit BridgeManager(pid_t target_pid);
  ~BridgeManager();

  void run();

private:
  void setup_ros_execution();

  void on_mq_event(mqd_t fd, bool allow_delegation);
  void on_signal();

  void check_parent_alive();
  void check_connection_demand();
  void check_should_exit();

  void handle_create_request(const MqMsgBridge & req, bool allow_delegation);

  void remove_bridge_node_locked(const std::string & unique_key);

  void send_delegate_request(pid_t target_pid, const MqMsgBridge & req);

  std::string generate_unique_key(const MqMsgBridge & req);
  int get_agnocast_connection_count(const std::string & topic_name, bool is_r2a);
  void unregister_from_kernel(const std::string & topic_name);

  const pid_t target_pid_;
  rclcpp::Logger logger_;
  bool is_parent_alive_{true};
  bool shutdown_requested_ = false;

  BridgeIpcEventLoop event_loop_;
  BridgeLoader loader_;

  rclcpp::Node::SharedPtr container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;
  std::mutex executor_mutex_;

  std::map<std::string, std::shared_ptr<void>> active_bridges_;
};

}  // namespace agnocast

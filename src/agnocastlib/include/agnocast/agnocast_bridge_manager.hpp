#pragma once

#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"
#include "agnocast/agnocast_bridge_loader.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <memory>
#include <optional>

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
  enum class AddBridgeResult { SUCCESS, EXIST, ERROR };

  // Holds the state and requirements for a bridge that is not yet locally active.
  // This struct manages two states:
  // 1. Pending: Waiting to acquire ownership from the kernel or to delegate to a peer.
  // 2. Monitoring: Successfully delegated to another process, but kept here to monitor
  //    for ownership changes in case the current owner dies.
  struct BridgeInfo
  {
    std::optional<MqMsgBridge> req_r2a;
    std::optional<MqMsgBridge> req_a2r;
    // If true, we need to send a delegation request to the current owner.
    bool need_delegate = false;
    // The PID of the process we successfully delegated to.
    // Used to detect ownership changes during the monitoring phase.
    pid_t delegated_owner_pid = 0;
  };

  const pid_t target_pid_;
  rclcpp::Logger logger_;

  BridgeIpcEventLoop event_loop_;
  BridgeLoader loader_;

  bool is_parent_alive_ = true;
  bool shutdown_requested_ = false;

  rclcpp::Node::SharedPtr container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;

  // Holds ownership of the bridge objects currently running in this process.
  // Key: topic name with direction suffix.
  std::map<std::string, std::shared_ptr<void>> active_bridges_;
  // Tracks topic ownership and delegation status for incoming MQ requests.
  // Key: raw topic name without direction suffix.
  std::map<std::string, BridgeInfo> requested_bridges_;

  void start_ros_execution();

  void on_mq_create_request(mqd_t fd);
  void on_mq_delegation_request(mqd_t fd);
  void on_signal();

  void register_create_request(const MqMsgBridge & req);
  void register_delegate_request(const MqMsgBridge & req);

  static AddBridgeResult try_add_bridge_to_kernel(
    const std::string & topic_name, pid_t & out_owner_pid);
  bool try_activate_bridge(const MqMsgBridge & req, const std::string & topic_name_with_direction);
  bool try_send_delegation(const MqMsgBridge & req, pid_t owner_pid);

  void check_parent_alive();
  void check_active_bridges();
  void check_requested_bridges();
  void check_should_exit();

  int get_agnocast_subscriber_count(const std::string & topic_name);
  int get_agnocast_publisher_count(const std::string & topic_name);
  void remove_active_bridge(const std::string & topic_name_with_direction);

  static std::pair<std::string, std::string> extract_topic_info(const MqMsgBridge & req);
};

}  // namespace agnocast

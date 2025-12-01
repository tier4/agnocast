#pragma once

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
#include <utility>
#include <vector>

namespace agnocast
{

extern int agnocast_fd;

using BridgeFn = std::shared_ptr<void> (*)(rclcpp::Node::SharedPtr, const BridgeTargetInfo &);

class BridgeGenerator
{
public:
  // =========================================================================
  // Constructor & Destructor
  // =========================================================================
  explicit BridgeGenerator(pid_t target_pid);
  ~BridgeGenerator();

  BridgeGenerator(const BridgeGenerator &) = delete;
  BridgeGenerator & operator=(const BridgeGenerator &) = delete;
  BridgeGenerator(BridgeGenerator &&) = delete;
  BridgeGenerator & operator=(BridgeGenerator &&) = delete;

  // =========================================================================
  // Public Interface
  // =========================================================================
  void run();

private:
  // =========================================================================
  // Initialization Helpers
  // =========================================================================
  void setup_mq();
  void setup_signals();
  void setup_epoll();
  void setup_ros_execution();

  // =========================================================================
  // Event Loop Handlers
  // =========================================================================
  void handle_epoll_events(const struct epoll_event * events, int count);
  void handle_mq_event(mqd_t fd, bool allow_delegation);
  void handle_signal_event();

  // =========================================================================
  // Lifecycle Management & GC
  // =========================================================================
  void check_parent_alive();
  void check_connection_demand();
  void check_should_exit();

  // =========================================================================
  // Bridge Logic (High Level)
  // =========================================================================
  void create_bridge_safely(const MqMsgBridge & req, const std::string & unique_key);
  void remove_bridge_node_locked(const std::string & unique_key);
  void load_and_add_node(const MqMsgBridge & req, const std::string & unique_key);

  // =========================================================================
  // Dynamic Loading Helpers
  // =========================================================================
  std::pair<void *, uintptr_t> load_library_base(const char * lib_path, const char * symbol_name);

  std::pair<BridgeFn, std::shared_ptr<void>> resolve_factory_function(
    const MqMsgBridge & req, const std::string & unique_key);

  std::shared_ptr<void> create_bridge_instance(
    BridgeFn entry_func, std::shared_ptr<void> lib_handle, const BridgeTargetInfo & target);

  // =========================================================================
  // IPC & Kernel Helpers
  // =========================================================================
  void send_delegate_request(pid_t target_pid, const MqMsgBridge & req);
  void unregister_from_kernel(const std::string & topic_name);
  int get_agnocast_connection_count(const std::string & topic_name, bool is_r2a);

  // =========================================================================
  // Member Variables
  // =========================================================================

  // --- Configuration & State ---
  const pid_t target_pid_;
  rclcpp::Logger logger_;
  bool is_parent_alive_{true};
  bool shutdown_requested_ = false;

  // --- File Descriptors & Resources ---
  int epoll_fd_ = -1;
  int signal_fd_ = -1;

  mqd_t mq_parent_fd_ = (mqd_t)-1;
  mqd_t mq_child_fd_ = (mqd_t)-1;
  std::string mq_parent_name_;
  std::string mq_child_name_;

  // --- ROS Execution Environment ---
  rclcpp::Node::SharedPtr container_node_;
  std::shared_ptr<agnocast::MultiThreadedAgnocastExecutor> executor_;
  std::thread executor_thread_;
  std::mutex executor_mutex_;

  // --- Data Structures ---
  std::map<std::string, std::shared_ptr<void>> active_bridges_;
  std::map<std::string, std::pair<BridgeFn, std::shared_ptr<void>>> cached_factories_;
};

}  // namespace agnocast
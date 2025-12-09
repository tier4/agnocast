#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"

#include "agnocast/agnocast_bridge_manager.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <signal.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <unistd.h>

#include <chrono>
#include <cstring>
#include <stdexcept>

// TODO: extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

BridgeManager::BridgeManager(pid_t target_pid)
: target_pid_(target_pid),
  logger_(rclcpp::get_logger("agnocast_bridge_manager")),
  event_loop_(target_pid, logger_),
  loader_(logger_)
{
  // TODO: Verify target parent process is alive (`kill` check)
  // TODO: Initialize ROS 2 (`rclcpp::init`)
  // TODO: Initialize heap hook daemon (`agnocast_heaphook_init_daemon`)
}

BridgeManager::~BridgeManager()
{
  // TODO: Cancel executor and join the executor thread
  // TODO: Shutdown ROS 2 (`rclcpp::shutdown`)
}

void BridgeManager::run()
{
  // 1. Setup ROS node and executor thread
  setup_ros_execution();

  // 2. Register Event Loop callbacks
  event_loop_.set_parent_mq_handler([this](int fd) { this->on_mq_event(fd, true); });
  event_loop_.set_child_mq_handler([this](int fd) { this->on_mq_event(fd, false); });
  event_loop_.set_signal_handler([this]() { this->on_signal(); });

  // 3. Main Loop
  while (!shutdown_requested_ && rclcpp::ok()) {
    check_parent_alive();

    // TODO: Periodically (e.g., every 1s):
    //   - check_connection_demand() (Garbage Collection)
    //   - check_should_exit()

    if (shutdown_requested_) break;

    event_loop_.spin_once(1000);
  }
}

void BridgeManager::setup_ros_execution()
{
  // TODO: Create `container_node_`
  // TODO: Create `MultiThreadedAgnocastExecutor` and add node
  // TODO: Spawn `executor_thread_` to run `executor_->spin()`
}

void BridgeManager::on_mq_event(mqd_t fd, bool allow_delegation)
{
  // TODO: Loop `mq_receive` to get all pending requests
  // TODO: Call `handle_create_request` for each request
}

void BridgeManager::on_signal()
{
  // TODO: Log shutdown and set `shutdown_requested_` = true
  // TODO: Cancel the ROS executor
}

void BridgeManager::handle_create_request(const MqMsgBridge & req, bool allow_delegation)
{
  // TODO: Generate unique key and lock mutex
  // TODO: Check if bridge already exists locally

  // TODO: Try `ioctl` (AGNOCAST_REGISTER_BRIDGE_CMD)
  //   - If Success:
  //       - Call `loader_.load_and_create`
  //       - Store new bridge in `active_bridges_`
  //   - If Fail (EEXIST) && allow_delegation:
  //       - Call `ioctl` (AGNOCAST_GET_BRIDGE_PID_CMD) to find owner
  //       - Call `send_delegate_request` to forward request to owner
}

void BridgeManager::remove_bridge_node_locked(const std::string & unique_key)
{
  // TODO: Remove bridge from `active_bridges_` map

  // TODO: Check if the pair (reverse direction) is also gone
  // TODO: If both gone, call `unregister_from_kernel`

  check_should_exit();
}

void BridgeManager::check_connection_demand()
{
  // TODO: Lock mutex
  // TODO: Iterate through active bridges
  // TODO: Call `get_agnocast_connection_count` for each topic
  // TODO: If count is below threshold, add to remove list
  // TODO: Call `remove_bridge_node_locked` for items in remove list
}

void BridgeManager::check_should_exit()
{
  // TODO: If parent is dead AND `active_bridges_` is empty -> trigger shutdown
}

void BridgeManager::check_parent_alive()
{
  // TODO: Check if parent PID is alive (`kill`)
  // TODO: If dead: set flag, close parent MQ, and call `check_should_exit`
}

std::string BridgeManager::generate_unique_key(const MqMsgBridge & req)
{
  // TODO: Generate key based on topic name and direction (e.g., "topic_R2A")
  return "";
}

int BridgeManager::get_agnocast_connection_count(const std::string & topic_name, bool is_r2a)
{
  // TODO: Call `ioctl` (GET_SUBSCRIBER_NUM or GET_PUBLISHER_NUM) based on direction
  return 0;
}

void BridgeManager::unregister_from_kernel(const std::string & topic_name)
{
  // TODO: Call `ioctl` (AGNOCAST_UNREGISTER_BRIDGE_CMD)
}

void BridgeManager::send_delegate_request(pid_t target_pid, const MqMsgBridge & req)
{
  // TODO: Open child MQ of target PID
  // TODO: Send request via `mq_send`
}

}  // namespace agnocast

#pragma GCC diagnostic pop

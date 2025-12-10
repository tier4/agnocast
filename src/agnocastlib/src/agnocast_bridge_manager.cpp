#include "agnocast/agnocast_bridge_manager.hpp"

#include <sys/prctl.h>
#include <unistd.h>

#include <csignal>
#include <stdexcept>
#include <string>

namespace agnocast
{

BridgeManager::BridgeManager(pid_t target_pid)
: target_pid_(target_pid),
  logger_(rclcpp::get_logger("agnocast_bridge_manager")),
  event_loop_(target_pid, logger_),
  loader_(logger_)
{
  // Optimization: Fail-fast to avoid rclcpp::init overhead.
  // Note that the process ensures correct termination even without this check.
  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  rclcpp::InitOptions init_options{};
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  // TODO(yutarokobayashi): heaphook init
}

BridgeManager::~BridgeManager()
{
  if (executor_) {
    executor_->cancel();
  }
  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void BridgeManager::run()
{
  std::string proc_name = "agno_br_" + std::to_string(getpid());
  prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0);

  start_ros_execution();

  // TODO(yutarokobayashi): Setup event_loop handler.

  while (!shutdown_requested_) {
    check_parent_alive();
    check_active_bridges();
    check_should_exit();

    if (shutdown_requested_) {
      break;
    }

    // TODO(yutarokobayashi): Run the loop only once. Wait for 1s to avoid busy looping.
  }
}

void BridgeManager::start_ros_execution()
{
  std::string node_name = "agnocast_bridge_node_" + std::to_string(getpid());
  container_node_ = std::make_shared<rclcpp::Node>(node_name);

  executor_ = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>();
  executor_->add_node(container_node_);

  executor_thread_ = std::thread([this]() {
    try {
      this->executor_->spin();
    } catch (const std::exception & e) {
      RCLCPP_ERROR(logger_, "Executor Thread CRASHED: %s", e.what());
    }
  });
}

void BridgeManager::check_parent_alive()
{
  if (!is_parent_alive_) {
    return;
  }
  if (kill(target_pid_, 0) != 0) {
    is_parent_alive_ = false;
    // TODO(yutarokobayashi): close parent mq
  }
}

void BridgeManager::check_active_bridges()
{
  // TODO(yutarokobayashi): Verifying the number of connections and get remove bridge name
  remove_active_bridges("TOPIC_R2A");
}

void BridgeManager::check_should_exit()
{
  if (!is_parent_alive_ && active_bridges_.empty()) {
    shutdown_requested_ = true;
    if (executor_) {
      executor_->cancel();
    }
  }
}

void BridgeManager::remove_active_bridges(const std::string & topic_name_with_dirction)
{
  if (!active_bridges_.count(topic_name_with_dirction)) return;

  active_bridges_.erase(topic_name_with_dirction);
  // TODO(yutarokobayashi): Unregister from the kernel only if the paired bridge in the reverse
  // direction is also missing.
}

}  // namespace agnocast

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
  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void BridgeManager::run()  // NOLINT(readability-convert-member-functions-to-static)
{
  std::string proc_name = "agno_br_" + std::to_string(getpid());
  prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0);

  start_ros_execution();

  // TODO(yutarokobayashi): event_loop_;
}

void BridgeManager::start_ros_execution()
{
  std::string node_name = "agnocast_bridge_node_" + std::to_string(getpid());
  container_node_ = std::make_shared<rclcpp::Node>(node_name);

  executor_ =
    std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(rclcpp::ExecutorOptions(), 0, 0);
  executor_->add_node(container_node_);

  executor_thread_ = std::thread([this]() {
    try {
      this->executor_->spin();
    } catch (const std::exception & e) {
      RCLCPP_ERROR(logger_, "Executor Thread CRASHED: %s", e.what());
    }
  });
}

}  // namespace agnocast

#include "agnocast/agnocast_bridge_manager.hpp"

#include <signal.h>
#include <unistd.h>

#include <stdexcept>

namespace agnocast
{

BridgeManager::BridgeManager(pid_t target_pid)
: target_pid_(target_pid),
  logger_(rclcpp::get_logger("agnocast_bridge_manager")),
  event_loop_(target_pid, logger_),
  loader_(logger_)
{
  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  rclcpp::InitOptions init_options;
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  // TODO: heaphook init
}

BridgeManager::~BridgeManager()
{
  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

}  // namespace agnocast

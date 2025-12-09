#include "agnocast/agnocast_bridge_manager.hpp"

#include <sys/prctl.h>
#include <unistd.h>

#include <csignal>
#include <stdexcept>
#include <string>

extern "C" bool init_child_allocator();

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

  if (!init_child_allocator()) {
    RCLCPP_ERROR(logger_, "[Bridge] Heaphook init failed: Could not attach to shared memory pool.");
  }
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

  // TODO(yutarokobayashi): event_loop_;
}

}  // namespace agnocast

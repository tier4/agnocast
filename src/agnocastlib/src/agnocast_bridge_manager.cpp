#include "agnocast/agnocast_bridge_manager.hpp"

#include <dlfcn.h>
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

  void * handle = dlopen(NULL, RTLD_NOW);
  if (!handle) {
    RCLCPP_ERROR(logger_, "[Bridge] Heaphook init failed: Could not open symbol table.");
    exit(EXIT_FAILURE);
  }

  auto init_child_allocator = reinterpret_cast<bool (*)()>(dlsym(handle, "init_child_allocator"));

  const char * dlsym_error = dlerror();
  if (dlsym_error || !init_child_allocator) {
    RCLCPP_ERROR(
      logger_,
      "[Bridge] Heaphook init failed: Symbol 'init_child_allocator' not found. "
      "Error: %s. Make sure libagnocast_heaphook.so is loaded via LD_PRELOAD.",
      dlsym_error ? dlsym_error : "Symbol is null");
    dlclose(handle);
    throw std::runtime_error("Heaphook symbol lookup failed");
  }

  if (!init_child_allocator()) {
    RCLCPP_ERROR(logger_, "[Bridge] Heaphook init failed: Could not attach to shared memory pool.");
    dlclose(handle);
    exit(EXIT_FAILURE);
  }

  dlclose(handle);
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

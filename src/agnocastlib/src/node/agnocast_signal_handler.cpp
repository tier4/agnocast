#include "agnocast_signal_handler.hpp"

#include "rclcpp/rclcpp.hpp"

#include <unistd.h>

#include <csignal>
#include <cstring>

namespace agnocast
{

namespace
{
rclcpp::Logger logger = rclcpp::get_logger("agnocast_signal_handler");

std::array<volatile int, SignalHandler::MAX_EXECUTORS_NUM> make_initial_eventfds()
{
  std::array<volatile int, SignalHandler::MAX_EXECUTORS_NUM> arr;
  for (auto & fd : arr) {
    fd = -1;
  }
  return arr;
}
}  // namespace

std::atomic<bool> SignalHandler::installed_{false};
volatile sig_atomic_t SignalHandler::shutdown_requested_{0};
std::mutex SignalHandler::eventfds_mutex_;
std::array<volatile int, SignalHandler::MAX_EXECUTORS_NUM> SignalHandler::eventfds_ =
  make_initial_eventfds();
std::atomic<size_t> SignalHandler::eventfd_count_{0};
struct sigaction SignalHandler::old_sigint_action_{};
struct sigaction SignalHandler::old_sigterm_action_{};

void SignalHandler::install()
{
  // eventfds_ is already initialized to -1 at static initialization
  if (installed_.exchange(true)) {
    return;
  }

  struct sigaction sa
  {
  };
  sigemptyset(&sa.sa_mask);
  sa.sa_handler = &SignalHandler::signal_handler;

  if (sigaction(SIGINT, &sa, &old_sigint_action_) != 0) {
    RCLCPP_ERROR(logger, "Failed to install SIGINT handler: %s", strerror(errno));
    exit(EXIT_FAILURE);
  }

  if (sigaction(SIGTERM, &sa, &old_sigterm_action_) != 0) {
    RCLCPP_ERROR(logger, "Failed to install SIGTERM handler: %s", strerror(errno));
    exit(EXIT_FAILURE);
  }
}

void SignalHandler::uninstall()
{
  if (!installed_.exchange(false)) {
    return;
  }

  if (sigaction(SIGINT, &old_sigint_action_, nullptr) != 0) {
    RCLCPP_ERROR(logger, "Failed to restore SIGINT handler: %s", strerror(errno));
  }

  if (sigaction(SIGTERM, &old_sigterm_action_, nullptr) != 0) {
    RCLCPP_ERROR(logger, "Failed to restore SIGTERM handler: %s", strerror(errno));
  }
}

void SignalHandler::register_shutdown_event(int eventfd)
{
  std::lock_guard<std::mutex> lock(eventfds_mutex_);
  size_t count = eventfd_count_.load();

  for (size_t i = 0; i < count; ++i) {
    if (eventfds_[i] == -1) {
      eventfds_[i] = eventfd;
      return;
    }
  }

  if (count >= MAX_EXECUTORS_NUM) {
    RCLCPP_ERROR(logger, "Maximum number of executors (%zu) exceeded", MAX_EXECUTORS_NUM);
    return;
  }
  eventfds_[count] = eventfd;
  eventfd_count_.store(count + 1);
}

void SignalHandler::unregister_shutdown_event(int eventfd)
{
  std::lock_guard<std::mutex> lock(eventfds_mutex_);
  size_t count = eventfd_count_.load();
  for (size_t i = 0; i < count; ++i) {
    if (eventfds_[i] == eventfd) {
      eventfds_[i] = -1;
      return;
    }
  }
}

void SignalHandler::signal_handler(int signum)
{
  (void)signum;
  // Use volatile sig_atomic_t assignment for async-signal-safety
  shutdown_requested_ = 1;
  notify_all_executors();
}

void SignalHandler::notify_all_executors()
{
  // This function is async-signal-safe:
  // - volatile int read is safe
  // - write() is async-signal-safe per POSIX
  uint64_t val = 1;
  for (size_t i = 0; i < MAX_EXECUTORS_NUM; ++i) {
    int fd = eventfds_[i];
    if (fd != -1) {
      [[maybe_unused]] auto ret = write(fd, &val, sizeof(val));
    }
  }
}

}  // namespace agnocast

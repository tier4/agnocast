#pragma once

#include <array>
#include <atomic>
#include <csignal>
#include <mutex>

namespace agnocast
{

class SignalHandler
{
public:
  static void install();
  static void uninstall();
  static bool is_shutdown_requested() { return shutdown_requested_ != 0; }
  static void request_shutdown() { shutdown_requested_ = 1; }
  static void register_shutdown_event(int eventfd);
  static void unregister_shutdown_event(int eventfd);
  static void notify_all_executors();

  static constexpr size_t MAX_EXECUTORS_NUM = 128;

private:

  static std::atomic<bool> installed_;
  // Use volatile sig_atomic_t for async-signal-safety
  static volatile sig_atomic_t shutdown_requested_;

  static std::mutex eventfds_mutex_;
  // Use volatile int array for async-signal-safe access from signal handler
  static std::array<volatile int, MAX_EXECUTORS_NUM> eventfds_;
  static std::atomic<size_t> eventfd_count_;

  static struct sigaction old_sigint_action_;
  static struct sigaction old_sigterm_action_;

  static void signal_handler(int signum);
};

}  // namespace agnocast

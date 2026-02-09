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
  static void register_shutdown_event(int eventfd);
  static void unregister_shutdown_event(int eventfd);

private:
  static constexpr size_t MAX_EXECUTORS_NUM = 128;

  static std::atomic<bool> installed_;

  static std::mutex eventfds_mutex_;
  // volatile sig_atomic_t is async-signal-safe per C/POSIX standard
  static std::array<volatile sig_atomic_t, MAX_EXECUTORS_NUM> eventfds_;
  static std::atomic<size_t> eventfd_count_;

  static void signal_handler(int signum);
  static void notify_all_executors();
  static std::array<volatile sig_atomic_t, MAX_EXECUTORS_NUM> make_initial_eventfds();
};

}  // namespace agnocast

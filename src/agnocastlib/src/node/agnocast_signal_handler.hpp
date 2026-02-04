#pragma once

#include <array>
#include <atomic>
#include <mutex>

namespace agnocast
{

class SignalHandler
{
public:
  static void install();
  static bool is_shutdown_requested() { return shutdown_requested_.load(); }
  static void register_shutdown_event(int eventfd);
  static void unregister_shutdown_event(int eventfd);

private:
  static constexpr size_t MAX_EXECUTORS_NUM = 128;

  static std::atomic<bool> installed_;
  static std::atomic<bool> shutdown_requested_;

  static std::mutex eventfds_mutex_;
  static std::array<std::atomic<int>, MAX_EXECUTORS_NUM> eventfds_;
  static std::atomic<size_t> eventfd_count_;

  static void signal_handler(int signum);
  static void notify_all_executors();
};

}  // namespace agnocast

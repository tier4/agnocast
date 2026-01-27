#pragma once

#include "agnocast/agnocast_timer.hpp"
#include "rclcpp/rclcpp.hpp"

#include <atomic>
#include <chrono>
#include <functional>
#include <memory>
#include <mutex>
#include <unordered_map>

namespace agnocast
{

constexpr int64_t NANOSECONDS_PER_SECOND = 1000000000;

inline int64_t to_nanoseconds(const std::chrono::steady_clock::time_point & tp)
{
  return std::chrono::duration_cast<std::chrono::nanoseconds>(tp.time_since_epoch()).count();
}

struct TimerInfo
{
  ~TimerInfo();

  int timer_fd = -1;
  std::weak_ptr<TimerBase> timer;
  std::function<void(TimerCallbackInfo &)> callback;  // for tf2 timers (when timer is empty)
  rclcpp::CallbackGroup::SharedPtr callback_group;
  std::atomic<int64_t> last_call_time_ns;
  std::atomic<int64_t> next_call_time_ns;
  std::chrono::nanoseconds period;
  bool need_epoll_update = true;
  bool is_canceled = false;

  // Clock-based timer support (nullptr means steady_clock)
  rclcpp::Clock::SharedPtr clock;
  // Time Jump handler for ROS_TIME
  rclcpp::JumpHandler::SharedPtr jump_handler;
};

extern std::mutex id2_timer_info_mtx;
extern std::unordered_map<uint32_t, std::shared_ptr<TimerInfo>> id2_timer_info;
extern std::atomic<uint32_t> next_timer_id;

int create_timer_fd(std::chrono::nanoseconds period);

void handle_timer_event(TimerInfo & timer_info);

uint32_t allocate_timer_id();

void register_timer_info(
  uint32_t timer_id, std::shared_ptr<TimerBase> timer, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr & callback_group);

void unregister_timer_info(uint32_t timer_id);

void register_timer_info_with_clock(
  uint32_t timer_id, std::shared_ptr<TimerBase> timer, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr & callback_group, rclcpp::Clock::SharedPtr clock);

// tf2 timer API functions
uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  rclcpp::CallbackGroup::SharedPtr callback_group);

void cancel_timer(uint32_t timer_id);
void reset_timer(uint32_t timer_id);
void remove_timer(uint32_t timer_id);

}  // namespace agnocast

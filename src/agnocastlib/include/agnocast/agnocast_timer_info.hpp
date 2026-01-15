#pragma once

#include "rclcpp/callback_group.hpp"

#include <atomic>
#include <chrono>
#include <functional>
#include <mutex>
#include <unordered_map>

namespace agnocast
{

struct TimerCallbackInfo
{
  std::chrono::steady_clock::time_point expected_call_time;
  std::chrono::steady_clock::time_point actual_call_time;
};

struct TimerInfo
{
  int timer_fd;
  std::function<void(TimerCallbackInfo &)> callback;
  std::chrono::steady_clock::time_point next_call_time;
  std::chrono::nanoseconds period;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  bool need_epoll_update = true;
  bool is_canceled = false;
};

extern std::mutex id2_timer_info_mtx;
extern std::unordered_map<uint32_t, TimerInfo> id2_timer_info;
extern std::atomic<uint32_t> next_timer_id;

int create_timer_fd(std::chrono::nanoseconds period);

void handle_timer_event(TimerInfo & timer_info);

uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group);

/// \brief Cancel a timer (stop it from firing, but keep it registered)
/// \param timer_id The timer ID returned by register_timer
/// \throws std::out_of_range if timer_id is not found
void cancel_timer(uint32_t timer_id);

/// \brief Reset a canceled timer (re-arm it to fire again)
/// \param timer_id The timer ID returned by register_timer
/// \throws std::out_of_range if timer_id is not found
void reset_timer(uint32_t timer_id);

/// \brief Remove a timer completely (close fd and unregister)
/// \param timer_id The timer ID returned by register_timer
/// \throws std::out_of_range if timer_id is not found
void remove_timer(uint32_t timer_id);

}  // namespace agnocast

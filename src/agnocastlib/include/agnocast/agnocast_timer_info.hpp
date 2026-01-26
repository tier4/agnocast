#pragma once

#include "agnocast/timer.hpp"
#include "rclcpp/rclcpp.hpp"

#include <atomic>
#include <chrono>
#include <functional>
#include <memory>
#include <mutex>
#include <unordered_map>

namespace agnocast
{

inline int64_t to_nanoseconds(const std::chrono::steady_clock::time_point & tp)
{
  return std::chrono::duration_cast<std::chrono::nanoseconds>(tp.time_since_epoch()).count();
}

struct TimerInfo
{
  int timer_fd;
  std::weak_ptr<TimerBase> timer;
  std::chrono::steady_clock::time_point next_call_time;
  std::chrono::nanoseconds period;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  bool need_epoll_update = true;
};

extern std::mutex id2_timer_info_mtx;
extern std::unordered_map<uint32_t, std::shared_ptr<TimerInfo>> id2_timer_info;
extern std::atomic<uint32_t> next_timer_id;

int create_timer_fd(uint32_t timer_id, std::chrono::nanoseconds period);

void handle_timer_event(TimerInfo & timer_info);

uint32_t allocate_timer_id();

void register_timer_info(
  uint32_t timer_id, std::shared_ptr<TimerBase> timer, std::chrono::nanoseconds period,
  rclcpp::CallbackGroup::SharedPtr callback_group);

}  // namespace agnocast

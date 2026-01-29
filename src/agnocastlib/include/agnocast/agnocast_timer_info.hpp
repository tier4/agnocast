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

struct TimerInfo
{
  ~TimerInfo();

  uint32_t timer_id = 0;
  int timer_fd = -1;
  int clock_eventfd = -1;  // eventfd to wake epoll on clock updates (ROS_TIME only)
  std::weak_ptr<TimerBase> timer;
  std::function<void(TimerCallbackInfo &)> callback;  // for tf2 timers (when timer is empty)
  rclcpp::CallbackGroup::SharedPtr callback_group;
  std::atomic<int64_t> last_call_time_ns;
  std::atomic<int64_t> next_call_time_ns;
  std::atomic<int64_t> time_credit{
    0};  // Credit for time elapsed before ROS time is activated/deactivated
  std::chrono::nanoseconds period;
  bool need_epoll_update = true;
  bool is_canceled = false;

  rclcpp::Clock::SharedPtr clock;
  rclcpp::JumpHandler::SharedPtr jump_handler;
};

extern std::mutex id2_timer_info_mtx;
extern std::unordered_map<uint32_t, std::shared_ptr<TimerInfo>> id2_timer_info;
extern std::atomic<uint32_t> next_timer_id;

int create_timer_fd(std::chrono::nanoseconds period);

void handle_timer_event(TimerInfo & timer_info);

void handle_clock_event(TimerInfo & timer_info);

uint32_t allocate_timer_id();

void register_timer_info(
  uint32_t timer_id, std::shared_ptr<TimerBase> timer, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr & callback_group, rclcpp::Clock::SharedPtr clock);

void unregister_timer_info(uint32_t timer_id);

// tf2 timer API functions
uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  rclcpp::CallbackGroup::SharedPtr callback_group);

void cancel_timer(uint32_t timer_id);
void reset_timer(uint32_t timer_id);
void remove_timer(uint32_t timer_id);

}  // namespace agnocast

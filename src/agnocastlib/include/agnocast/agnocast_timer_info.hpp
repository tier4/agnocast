#pragma once

#include "agnocast/agnocast_timer.hpp"
#include "rclcpp/callback_group.hpp"

#include <atomic>
#include <memory>
#include <mutex>
#include <unordered_map>

namespace agnocast
{

struct TimerInfo
{
  std::shared_ptr<AgnocastTimer> timer;
  int timer_fd;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  bool need_epoll_update = true;
};

extern std::mutex id2_timer_info_mtx;
extern std::unordered_map<uint32_t, TimerInfo> id2_timer_info;
extern std::atomic<uint32_t> next_timer_id;

uint32_t register_timer(
  std::function<void()> callback, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group);

}  // namespace agnocast

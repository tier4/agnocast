// Copyright 2025 Agnocast
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef AGNOCAST__AGNOCAST_TIMER_INFO_HPP_
#define AGNOCAST__AGNOCAST_TIMER_INFO_HPP_

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

/**
 * @brief Register a timer with the Agnocast executor
 *
 * @param callback Function to call when timer expires
 * @param period Timer period in nanoseconds
 * @param callback_group Callback group for thread safety
 * @return uint32_t Timer ID
 */
uint32_t register_timer(
  std::function<void()> callback,
  std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group);

}  // namespace agnocast

#endif  // AGNOCAST__AGNOCAST_TIMER_INFO_HPP_

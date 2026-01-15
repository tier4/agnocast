// Copyright 2024 The Agnocast Authors.
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

#include "agnocast/node/tf2/create_timer_agnocast.hpp"

#include <chrono>
#include <stdexcept>

namespace agnocast
{

tf2_ros::TimerHandle CreateTimerAgnocast::createTimer(
  rclcpp::Clock::SharedPtr /*clock*/, const tf2::Duration & period,
  tf2_ros::TimerCallbackType callback)
{
  std::lock_guard<std::mutex> lock(mutex_);

  const auto handle = next_handle_++;

  // Convert tf2::Duration to std::chrono::nanoseconds
  const auto period_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(period);

  // Create wrapper callback that calls tf2's callback with the handle
  auto wrapper_callback = [callback, handle](TimerCallbackInfo &) { callback(handle); };

  // Register with agnocast's timer system (no callback group needed for tf2 timers)
  const uint32_t timer_id = register_timer(wrapper_callback, period_ns, nullptr);

  handle_to_timer_id_[handle] = timer_id;

  return handle;
}

void CreateTimerAgnocast::cancel(const tf2_ros::TimerHandle & timer_handle)
{
  std::lock_guard<std::mutex> lock(mutex_);

  auto it = handle_to_timer_id_.find(timer_handle);
  if (it == handle_to_timer_id_.end()) {
    throw tf2_ros::InvalidTimerHandleException("Invalid timer handle in cancel()");
  }

  try {
    cancel_timer(it->second);
  } catch (const std::out_of_range &) {
    throw tf2_ros::InvalidTimerHandleException("Timer not found in cancel()");
  }
}

void CreateTimerAgnocast::reset(const tf2_ros::TimerHandle & timer_handle)
{
  std::lock_guard<std::mutex> lock(mutex_);

  auto it = handle_to_timer_id_.find(timer_handle);
  if (it == handle_to_timer_id_.end()) {
    throw tf2_ros::InvalidTimerHandleException("Invalid timer handle in reset()");
  }

  try {
    reset_timer(it->second);
  } catch (const std::out_of_range &) {
    throw tf2_ros::InvalidTimerHandleException("Timer not found in reset()");
  }
}

void CreateTimerAgnocast::remove(const tf2_ros::TimerHandle & timer_handle)
{
  std::lock_guard<std::mutex> lock(mutex_);

  auto it = handle_to_timer_id_.find(timer_handle);
  if (it == handle_to_timer_id_.end()) {
    throw tf2_ros::InvalidTimerHandleException("Invalid timer handle in remove()");
  }

  try {
    remove_timer(it->second);
  } catch (const std::out_of_range &) {
    throw tf2_ros::InvalidTimerHandleException("Timer not found in remove()");
  }

  handle_to_timer_id_.erase(it);
}

}  // namespace agnocast

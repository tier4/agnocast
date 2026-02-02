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

#include "agnocast/node/tf2/buffer.hpp"

#include "tf2/exceptions.h"
#include "tf2_ros/buffer_interface.h"

#include <chrono>
#include <thread>

namespace agnocast
{

namespace
{
constexpr char threading_error[] =
  "Do not call canTransform or lookupTransform with a timeout "
  "unless you are using another thread for populating data. Without a dedicated thread it will "
  "always timeout. If you have a separate thread servicing tf messages, call "
  "setUsingDedicatedThread(true) on your Buffer instance.";
}  // namespace

Buffer::Buffer(rclcpp::Clock::SharedPtr clock, tf2::Duration cache_time)
: tf2::BufferCore(cache_time), clock_(clock)
{
  if (nullptr == clock_) {
    throw std::invalid_argument("clock must be a valid instance");
  }

  // Set up time jump callback
  auto post_jump_cb = [this](const rcl_time_jump_t & jump_info) { onTimeJump(jump_info); };

  rcl_jump_threshold_t jump_threshold;
  // Disable forward jump callbacks
  jump_threshold.min_forward.nanoseconds = 0;
  // Anything backwards is a jump
  jump_threshold.min_backward.nanoseconds = -1;
  // Callback if the clock changes too
  jump_threshold.on_clock_change = true;

  jump_handler_ = clock_->create_jump_callback(nullptr, post_jump_cb, jump_threshold);
}

void Buffer::onTimeJump(const rcl_time_jump_t & jump)
{
  if (RCL_ROS_TIME_ACTIVATED == jump.clock_change ||
      RCL_ROS_TIME_DEACTIVATED == jump.clock_change)
  {
    RCLCPP_WARN(rclcpp::get_logger("agnocast_tf2_buffer"), "Detected time source change. Clearing TF buffer.");
    clear();
  } else if (jump.delta.nanoseconds < 0) {
    RCLCPP_WARN(rclcpp::get_logger("agnocast_tf2_buffer"), "Detected jump back in time. Clearing TF buffer.");
    clear();
  }
}

bool Buffer::checkAndErrorDedicatedThreadPresent(std::string * error_str) const
{
  if (isUsingDedicatedThread()) {
    return true;
  }

  if (error_str) {
    *error_str = threading_error;
  }

  RCLCPP_ERROR(rclcpp::get_logger("agnocast_tf2_buffer"), "%s", threading_error);
  return false;
}

bool Buffer::waitForTransformAvailable(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration & timeout, std::string * errstr) const
{
  // If timeout is zero, don't wait
  if (timeout <= tf2::Duration::zero()) {
    return BufferCore::canTransform(target_frame, source_frame, time, errstr);
  }

  const auto start_time = clock_->now();
  const auto timeout_duration = std::chrono::duration_cast<std::chrono::nanoseconds>(timeout);
  const auto end_time = start_time + rclcpp::Duration(timeout_duration);

  // Polling interval (10ms, same as tf2_ros::Buffer)
  const auto poll_interval = std::chrono::milliseconds(10);

  while (clock_->now() < end_time &&
         !BufferCore::canTransform(target_frame, source_frame, time, errstr) &&
         (clock_->now() + rclcpp::Duration(3, 0) >= start_time) &&  // don't wait if bag loop
         rclcpp::ok())
  {
    std::this_thread::sleep_for(poll_interval);
  }

  // Final check after timeout
  return BufferCore::canTransform(target_frame, source_frame, time, errstr);
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout) const
{
  // Pass error string to suppress console spam
  std::string error;
  canTransform(target_frame, source_frame, time, timeout, &error);
  return BufferCore::lookupTransform(target_frame, source_frame, time);
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout) const
{
  // Pass error string to suppress console spam
  std::string error;
  canTransform(target_frame, target_time, source_frame, source_time, fixed_frame, timeout, &error);
  return BufferCore::lookupTransform(
    target_frame, target_time, source_frame, source_time, fixed_frame);
}

bool Buffer::canTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout, std::string * errstr) const
{
  // Check dedicated thread if timeout is non-zero
  if (timeout > tf2::Duration::zero() && !checkAndErrorDedicatedThreadPresent(errstr)) {
    return false;
  }
  return waitForTransformAvailable(target_frame, source_frame, time, timeout, errstr);
}

bool Buffer::canTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout, std::string * errstr) const
{
  // Check dedicated thread if timeout is non-zero
  if (timeout > tf2::Duration::zero() && !checkAndErrorDedicatedThreadPresent(errstr)) {
    return false;
  }
  // Check if both transforms are available
  if (!waitForTransformAvailable(target_frame, fixed_frame, target_time, timeout, errstr)) {
    return false;
  }
  if (!waitForTransformAvailable(fixed_frame, source_frame, source_time, timeout, errstr)) {
    return false;
  }
  return true;
}

}  // namespace agnocast

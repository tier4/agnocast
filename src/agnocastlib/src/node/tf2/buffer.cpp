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

#include "tf2_ros/buffer_interface.h"

#include <chrono>
#include <thread>

namespace agnocast
{

Buffer::Buffer(rclcpp::Clock::SharedPtr clock, tf2::Duration cache_time)
: tf2::BufferCore(cache_time), clock_(clock)
{
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

  while (clock_->now() < end_time) {
    if (BufferCore::canTransform(target_frame, source_frame, time, errstr)) {
      return true;
    }
    std::this_thread::sleep_for(poll_interval);
  }

  // Final check after timeout
  return BufferCore::canTransform(target_frame, source_frame, time, errstr);
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout) const
{
  // Wait for the transform to become available
  std::string error_string;
  if (!waitForTransformAvailable(target_frame, source_frame, time, timeout, &error_string)) {
    // Let BufferCore throw the appropriate exception
  }

  // Get the transform from BufferCore
  const auto transform = BufferCore::lookupTransform(target_frame, source_frame, time);

  // tf2::TransformStamped is compatible with geometry_msgs::msg::TransformStamped
  geometry_msgs::msg::TransformStamped msg;
  msg.header.stamp = transform.header.stamp;
  msg.header.frame_id = transform.header.frame_id;
  msg.child_frame_id = transform.child_frame_id;
  msg.transform.translation.x = transform.transform.translation.x;
  msg.transform.translation.y = transform.transform.translation.y;
  msg.transform.translation.z = transform.transform.translation.z;
  msg.transform.rotation.x = transform.transform.rotation.x;
  msg.transform.rotation.y = transform.transform.rotation.y;
  msg.transform.rotation.z = transform.transform.rotation.z;
  msg.transform.rotation.w = transform.transform.rotation.w;

  return msg;
}

geometry_msgs::msg::TransformStamped Buffer::lookupTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout) const
{
  // Wait for both transforms to become available
  std::string error_string;

  // Wait for target_frame -> fixed_frame at target_time
  if (
    !waitForTransformAvailable(target_frame, fixed_frame, target_time, timeout, &error_string)) {
    // Let BufferCore throw the appropriate exception
  }

  // Wait for fixed_frame -> source_frame at source_time
  if (
    !waitForTransformAvailable(fixed_frame, source_frame, source_time, timeout, &error_string)) {
    // Let BufferCore throw the appropriate exception
  }

  // Get the transform from BufferCore
  const auto transform =
    BufferCore::lookupTransform(target_frame, target_time, source_frame, source_time, fixed_frame);

  // tf2::TransformStamped is compatible with geometry_msgs::msg::TransformStamped
  geometry_msgs::msg::TransformStamped msg;
  msg.header.stamp = transform.header.stamp;
  msg.header.frame_id = transform.header.frame_id;
  msg.child_frame_id = transform.child_frame_id;
  msg.transform.translation.x = transform.transform.translation.x;
  msg.transform.translation.y = transform.transform.translation.y;
  msg.transform.translation.z = transform.transform.translation.z;
  msg.transform.rotation.x = transform.transform.rotation.x;
  msg.transform.rotation.y = transform.transform.rotation.y;
  msg.transform.rotation.z = transform.transform.rotation.z;
  msg.transform.rotation.w = transform.transform.rotation.w;

  return msg;
}

bool Buffer::canTransform(
  const std::string & target_frame, const std::string & source_frame, const tf2::TimePoint & time,
  const tf2::Duration timeout, std::string * errstr) const
{
  return waitForTransformAvailable(target_frame, source_frame, time, timeout, errstr);
}

bool Buffer::canTransform(
  const std::string & target_frame, const tf2::TimePoint & target_time,
  const std::string & source_frame, const tf2::TimePoint & source_time,
  const std::string & fixed_frame, const tf2::Duration timeout, std::string * errstr) const
{
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

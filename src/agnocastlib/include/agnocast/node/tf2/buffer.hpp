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

#ifndef AGNOCAST__NODE__TF2__BUFFER_HPP_
#define AGNOCAST__NODE__TF2__BUFFER_HPP_

#include "rclcpp/clock.hpp"
#include "rclcpp/duration.hpp"
#include "rclcpp/logging.hpp"
#include "rclcpp/time.hpp"

#include "geometry_msgs/msg/transform_stamped.hpp"

#include "rcl/time.h"

#include "tf2/buffer_core.h"
#include "tf2/time.h"
#include "tf2_ros/buffer_interface.h"

#include <memory>
#include <string>

namespace agnocast
{

// Helper functions to convert between rclcpp and tf2 time types (same as tf2_ros)
inline tf2::TimePoint fromRclcpp(const rclcpp::Time & time)
{
  return tf2::TimePoint(std::chrono::nanoseconds(time.nanoseconds()));
}

inline tf2::Duration fromRclcpp(const rclcpp::Duration & duration)
{
  return tf2::Duration(std::chrono::nanoseconds(duration.nanoseconds()));
}

/// \brief A tf2 buffer implementation for Agnocast.
///
/// This class inherits from tf2::BufferCore for transform storage and computation,
/// tf2_ros::BufferInterface for synchronous operations, and
/// tf2_ros::AsyncBufferInterface for asynchronous operations.
///
/// This implementation is aligned with tf2_ros::Buffer.
class Buffer : public tf2::BufferCore,
               public tf2_ros::BufferInterface
{
public:
  using tf2::BufferCore::lookupTransform;
  using tf2::BufferCore::canTransform;
  using SharedPtr = std::shared_ptr<Buffer>;

  /// \brief Constructor
  /// \param clock The clock to use for timing operations
  /// \param cache_time How long to keep transform history (default: 10 seconds)
  explicit Buffer(
    rclcpp::Clock::SharedPtr clock,
    tf2::Duration cache_time = tf2::Duration(tf2::BUFFER_CORE_DEFAULT_CACHE_TIME));

  virtual ~Buffer() = default;

  // ========== Synchronous lookupTransform ==========

  /// \brief Get the transform between two frames by frame ID.
  ///
  /// \param target_frame The frame to which data should be transformed
  /// \param source_frame The frame where the data originated
  /// \param time The time at which the value of the transform is desired (0 = latest)
  /// \param timeout How long to block before failing
  /// \return The transform between the frames
  /// \throws tf2::LookupException, tf2::ConnectivityException,
  ///         tf2::ExtrapolationException, tf2::InvalidArgumentException
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame,
    const tf2::TimePoint & time, const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID (rclcpp overload).
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame,
    const rclcpp::Time & time,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0)) const
  {
    return lookupTransform(target_frame, source_frame, fromRclcpp(time), fromRclcpp(timeout));
  }

  /// \brief Get the transform between two frames by frame ID (advanced).
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID (advanced, rclcpp overload).
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const rclcpp::Time & target_time,
    const std::string & source_frame, const rclcpp::Time & source_time,
    const std::string & fixed_frame,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0)) const
  {
    return lookupTransform(
      target_frame, fromRclcpp(target_time), source_frame, fromRclcpp(source_time), fixed_frame,
      fromRclcpp(timeout));
  }

  // ========== Synchronous canTransform ==========

  /// \brief Test if a transform is possible
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame,
    const tf2::TimePoint & time, const tf2::Duration timeout,
    std::string * errstr = nullptr) const override;

  /// \brief Test if a transform is possible (rclcpp overload)
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame,
    const rclcpp::Time & time,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0),
    std::string * errstr = nullptr) const
  {
    return canTransform(target_frame, source_frame, fromRclcpp(time), fromRclcpp(timeout), errstr);
  }

  /// \brief Test if a transform is possible (advanced)
  bool canTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout,
    std::string * errstr = nullptr) const override;

  /// \brief Test if a transform is possible (advanced, rclcpp overload)
  bool canTransform(
    const std::string & target_frame, const rclcpp::Time & target_time,
    const std::string & source_frame, const rclcpp::Time & source_time,
    const std::string & fixed_frame,
    const rclcpp::Duration timeout = rclcpp::Duration::from_nanoseconds(0),
    std::string * errstr = nullptr) const
  {
    return canTransform(
      target_frame, fromRclcpp(target_time), source_frame, fromRclcpp(source_time), fixed_frame,
      fromRclcpp(timeout), errstr);
  }

  // ========== Configuration ==========

  /// \brief Get the clock used by this buffer
  rclcpp::Clock::SharedPtr getClock() const { return clock_; }

  /// \brief Set whether a dedicated thread is being used for TF updates.
  ///
  /// This is required before using canTransform or lookupTransform with a non-zero timeout.
  ///
  /// \param value True if a dedicated thread is servicing TF messages
  void setUsingDedicatedThread(bool value) { using_dedicated_thread_ = value; }

  /// \brief Check if a dedicated thread is being used for TF updates.
  bool isUsingDedicatedThread() const { return using_dedicated_thread_; }

private:
  rclcpp::Clock::SharedPtr clock_;

  /// \brief Whether a dedicated thread is servicing TF messages
  bool using_dedicated_thread_ = false;

  /// \brief Reference to a jump handler registered to the clock
  rclcpp::JumpHandler::SharedPtr jump_handler_;

  /// \brief Callback for time jumps (clears buffer on backward jumps or clock changes)
  void onTimeJump(const rcl_time_jump_t & jump);

  /// \brief Check if dedicated thread is present, log error if not
  bool checkAndErrorDedicatedThreadPresent(std::string * errstr) const;

  /// \brief Wait for transform to become available (polling-based, for sync operations)
  /// \return true if transform became available, false on timeout
  bool waitForTransformAvailable(
    const std::string & target_frame, const std::string & source_frame,
    const tf2::TimePoint & time, const tf2::Duration & timeout,
    std::string * errstr = nullptr) const;
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__BUFFER_HPP_

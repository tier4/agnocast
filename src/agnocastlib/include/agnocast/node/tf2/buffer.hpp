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
#include "rclcpp/time.hpp"

#include "geometry_msgs/msg/transform_stamped.hpp"

#include "tf2/buffer_core.h"
#include "tf2/time.h"
#include "tf2_ros/buffer_interface.h"

#include <memory>
#include <string>

namespace agnocast
{

/// \brief A tf2 buffer implementation for Agnocast.
///
/// This class inherits from tf2::BufferCore for transform storage and computation,
/// and implements tf2_ros::BufferInterface for ROS message compatibility.
///
/// Note: This implementation does not include async waiting (waitForTransform).
/// For async support, a future version may implement tf2_ros::AsyncBufferInterface.
class Buffer : public tf2::BufferCore, public tf2_ros::BufferInterface
{
public:
  using SharedPtr = std::shared_ptr<Buffer>;

  /// \brief Constructor
  /// \param clock The clock to use for timing operations
  /// \param cache_time How long to keep transform history (default: 10 seconds)
  explicit Buffer(
    rclcpp::Clock::SharedPtr clock,
    tf2::Duration cache_time = tf2::Duration(tf2::BUFFER_CORE_DEFAULT_CACHE_TIME));

  virtual ~Buffer() = default;

  /// \brief Get the transform between two frames by frame ID.
  ///
  /// \param target_frame The frame to which data should be transformed
  /// \param source_frame The frame where the data originated
  /// \param time The time at which the value of the transform is desired (0 = latest)
  /// \param timeout How long to block before failing (polling-based, requires spin)
  /// \return The transform between the frames
  /// \throws tf2::LookupException, tf2::ConnectivityException,
  ///         tf2::ExtrapolationException, tf2::InvalidArgumentException
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const std::string & source_frame,
    const tf2::TimePoint & time, const tf2::Duration timeout) const override;

  /// \brief Get the transform between two frames by frame ID (advanced).
  ///
  /// \param target_frame The frame to which data should be transformed
  /// \param target_time The time to which the data should be transformed
  /// \param source_frame The frame where the data originated
  /// \param source_time The time at which the source_frame should be evaluated
  /// \param fixed_frame The frame in which to assume the transform is constant in time
  /// \param timeout How long to block before failing
  /// \return The transform between the frames
  geometry_msgs::msg::TransformStamped lookupTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout) const override;

  /// \brief Test if a transform is possible
  ///
  /// \param target_frame The frame into which to transform
  /// \param source_frame The frame from which to transform
  /// \param time The time at which to transform
  /// \param timeout How long to block before failing
  /// \param errstr A pointer to a string which will be filled with why the transform failed
  /// \return True if the transform is possible, false otherwise
  bool canTransform(
    const std::string & target_frame, const std::string & source_frame,
    const tf2::TimePoint & time, const tf2::Duration timeout,
    std::string * errstr = nullptr) const override;

  /// \brief Test if a transform is possible (advanced)
  ///
  /// \param target_frame The frame into which to transform
  /// \param target_time The time into which to transform
  /// \param source_frame The frame from which to transform
  /// \param source_time The time from which to transform
  /// \param fixed_frame The frame in which to treat the transform as constant in time
  /// \param timeout How long to block before failing
  /// \param errstr A pointer to a string which will be filled with why the transform failed
  /// \return True if the transform is possible, false otherwise
  bool canTransform(
    const std::string & target_frame, const tf2::TimePoint & target_time,
    const std::string & source_frame, const tf2::TimePoint & source_time,
    const std::string & fixed_frame, const tf2::Duration timeout,
    std::string * errstr = nullptr) const override;

  /// \brief Get the clock used by this buffer
  rclcpp::Clock::SharedPtr getClock() const { return clock_; }

private:
  rclcpp::Clock::SharedPtr clock_;

  /// \brief Wait for transform to become available (polling-based)
  /// \return true if transform became available, false on timeout
  bool waitForTransformAvailable(
    const std::string & target_frame, const std::string & source_frame,
    const tf2::TimePoint & time, const tf2::Duration & timeout,
    std::string * errstr = nullptr) const;
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__BUFFER_HPP_

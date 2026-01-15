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

#ifndef AGNOCAST__NODE__TF2__CREATE_TIMER_AGNOCAST_HPP_
#define AGNOCAST__NODE__TF2__CREATE_TIMER_AGNOCAST_HPP_

#include "agnocast/agnocast_timer_info.hpp"

#include "tf2_ros/create_timer_interface.h"

#include <mutex>
#include <unordered_map>

namespace agnocast
{

/// \brief Agnocast implementation of tf2_ros::CreateTimerInterface.
///
/// This class provides timer functionality for tf2 using agnocast's
/// timerfd-based timer mechanism instead of rclcpp's timer infrastructure.
/// This allows tf2 to work with agnocast::Node without becoming a DDS participant.
class CreateTimerAgnocast : public tf2_ros::CreateTimerInterface
{
public:
  CreateTimerAgnocast() = default;
  virtual ~CreateTimerAgnocast() = default;

  /// \brief Create a new timer using agnocast's timerfd mechanism.
  /// \param clock The clock (currently ignored, agnocast uses CLOCK_MONOTONIC)
  /// \param period The interval at which the timer fires
  /// \param callback The callback function to execute every interval
  /// \return A handle to the created timer
  tf2_ros::TimerHandle createTimer(
    rclcpp::Clock::SharedPtr clock, const tf2::Duration & period,
    tf2_ros::TimerCallbackType callback) override;

  /// \brief Cancel a timer (stop it from firing).
  /// \param timer_handle Handle to the timer to cancel
  /// \throws tf2_ros::InvalidTimerHandleException if the timer does not exist
  void cancel(const tf2_ros::TimerHandle & timer_handle) override;

  /// \brief Reset the timer (re-arm it to fire again).
  /// \param timer_handle Handle to the timer to reset
  /// \throws tf2_ros::InvalidTimerHandleException if the timer does not exist
  void reset(const tf2_ros::TimerHandle & timer_handle) override;

  /// \brief Remove a timer completely.
  /// \param timer_handle Handle to the timer to remove
  /// \throws tf2_ros::InvalidTimerHandleException if the timer does not exist
  void remove(const tf2_ros::TimerHandle & timer_handle) override;

private:
  std::mutex mutex_;
  // Map from tf2 TimerHandle to agnocast timer_id
  std::unordered_map<tf2_ros::TimerHandle, uint32_t> handle_to_timer_id_;
  tf2_ros::TimerHandle next_handle_{0};
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__CREATE_TIMER_AGNOCAST_HPP_

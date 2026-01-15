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

#ifndef AGNOCAST__NODE__NODE_INTERFACES__NODE_TIMERS_HPP_
#define AGNOCAST__NODE__NODE_INTERFACES__NODE_TIMERS_HPP_

#include "agnocast/node/node_interfaces/node_base.hpp"

#include "rclcpp/callback_group.hpp"
#include "rclcpp/node_interfaces/node_timers_interface.hpp"
#include "rclcpp/timer.hpp"

#include <memory>

namespace agnocast::node_interfaces
{

/// \brief Implementation of NodeTimersInterface for Agnocast.
///
/// This class provides timer management for agnocast::Node, implementing the
/// rclcpp::node_interfaces::NodeTimersInterface to allow compatibility with
/// libraries that expect this interface (e.g., tf2_ros::CreateTimerROS).
///
/// Timers added through this interface are executed by the executor's
/// ros2_spin() thread, not by agnocast's internal timer mechanism.
class NodeTimers : public rclcpp::node_interfaces::NodeTimersInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTimers>;

  /// \brief Constructor
  /// \param node_base Pointer to the node's base interface
  explicit NodeTimers(NodeBase * node_base);

  virtual ~NodeTimers() = default;

  /// \brief Add a timer to the node.
  ///
  /// The timer will be added to the specified callback group (or the default
  /// callback group if none is specified). The timer will be executed by the
  /// executor when it fires.
  ///
  /// \param timer The timer to add
  /// \param callback_group The callback group to add the timer to (optional)
  void add_timer(
    rclcpp::TimerBase::SharedPtr timer,
    rclcpp::CallbackGroup::SharedPtr callback_group) override;

private:
  NodeBase * node_base_;
};

}  // namespace agnocast::node_interfaces

#endif  // AGNOCAST__NODE__NODE_INTERFACES__NODE_TIMERS_HPP_

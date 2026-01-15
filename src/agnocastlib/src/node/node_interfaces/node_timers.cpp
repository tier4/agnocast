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

#include "agnocast/node/node_interfaces/node_timers.hpp"

#include "rclcpp/logging.hpp"

#include <stdexcept>

namespace agnocast::node_interfaces
{

NodeTimers::NodeTimers(NodeBase * node_base) : node_base_(node_base)
{
}

void NodeTimers::add_timer(
  rclcpp::TimerBase::SharedPtr /*timer*/, rclcpp::CallbackGroup::SharedPtr /*callback_group*/)
{
  // TODO(agnocast): rclcpp::TimerBase is not supported in agnocast because:
  // 1. rclcpp::Timer requires DDS infrastructure (rcl_timer, rcl_wait)
  // 2. agnocast uses timerfd + epoll for timers to avoid DDS participation
  //
  // For tf2 timer functionality, use agnocast::CreateTimerAgnocast which implements
  // tf2_ros::CreateTimerInterface using agnocast's native timer mechanism.
  //
  // Example:
  //   auto timer_interface = std::make_shared<agnocast::CreateTimerAgnocast>();
  //   buffer.setCreateTimerInterface(timer_interface);
  throw std::runtime_error(
    "NodeTimers::add_timer is not supported in agnocast. "
    "rclcpp::Timer requires DDS infrastructure. "
    "For tf2 timers, use agnocast::CreateTimerAgnocast instead.");
}

}  // namespace agnocast::node_interfaces

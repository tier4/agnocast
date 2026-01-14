// Copyright 2017 Open Source Robotics Foundation, Inc.
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

#include "agnocast/node/time_source.hpp"

#include "agnocast/bridge/agnocast_bridge_node.hpp"
#include "agnocast/node/agnocast_node.hpp"
#include "rcl/time.h"
#include "rclcpp/parameter_client.hpp"

#include "rosgraph_msgs/msg/clock.hpp"

#include <memory>
#include <string>
#include <utility>

namespace agnocast
{

const std::string use_sim_time_name = "use_sim_time";

class TimeSource::NodeState final
{
public:
  NodeState(agnocast::Node * node, const rclcpp::QoS & qos);
  NodeState(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_interface,
    rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_interface,
    agnocast::Node * node, const rclcpp::QoS & qos);
  ~NodeState();

  // Attach a clock to be controlled by this TimeSource
  void attachClock(rclcpp::Clock::SharedPtr clock);

  // Detach the clock from this TimeSource
  void detachClock(rclcpp::Clock::SharedPtr clock);

private:
  // Enable ros time for the attached clock
  void enable_ros_time();

  // Disable ros time for the attached clock
  void disable_ros_time();

  // Set ros time for the attached clock
  void set_clock(const builtin_interfaces::msg::Time & msg_time);

  // Create clock subscription
  void create_clock_subscription();

  // Destroy clock subscription
  void destroy_clock_subscription();

  // Callback for clock subscription
  void clock_cb(const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg);

  // Node interfaces
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_;

  // Agnocast node for creating subscriptions
  agnocast::Node * agnocast_node_;

  // QoS for clock subscription
  rclcpp::QoS qos_;

  // Clock subscription
  agnocast::Subscription<rosgraph_msgs::msg::Clock>::SharedPtr clock_subscription_;

  // Attached clock (single clock for minimal version)
  rclcpp::Clock::SharedPtr clock_;

  // Whether ros time is active
  bool ros_time_active_{false};
};

TimeSource::NodeState::NodeState(agnocast::Node * node, const rclcpp::QoS & qos)
: NodeState(node->get_node_base_interface(), node->get_node_parameters_interface(), node, qos)
{
}

TimeSource::NodeState::NodeState(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_interface,
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_interface,
  agnocast::Node * node, const rclcpp::QoS & qos)
: node_base_(std::move(node_base_interface)),
  node_parameters_(std::move(node_parameters_interface)),
  agnocast_node_(node),
  qos_(qos)
{
  // Check and handle use_sim_time parameter
  rclcpp::Parameter use_sim_time_param;
  if (node_parameters_->get_parameter(use_sim_time_name, use_sim_time_param)) {
    if (use_sim_time_param.get_value<bool>()) {
      create_clock_subscription();
    }
  }
}

TimeSource::NodeState::~NodeState()
{
  destroy_clock_subscription();
  if (clock_) {
    disable_ros_time();
  }
}

void TimeSource::NodeState::attachClock(rclcpp::Clock::SharedPtr clock)
{
  if (clock->get_clock_type() != RCL_ROS_TIME) {
    throw std::invalid_argument("Cannot attach a clock that is not ROS_TIME");
  }

  clock_ = std::move(clock);

  if (ros_time_active_) {
    enable_ros_time();
  }
}

void TimeSource::NodeState::detachClock(rclcpp::Clock::SharedPtr clock)
{
  if (clock_ == clock) {
    disable_ros_time();
    clock_.reset();
  }
}

void TimeSource::NodeState::enable_ros_time()
{
  ros_time_active_ = true;
  if (clock_) {
    auto clock_handle = clock_->get_clock_handle();
    rcl_ret_t ret = rcl_enable_ros_time_override(clock_handle);
    if (ret != RCL_RET_OK) {
      throw std::runtime_error("Failed to enable ros_time_override: " + std::to_string(ret));
    }
  }
}

void TimeSource::NodeState::disable_ros_time()
{
  ros_time_active_ = false;
  if (clock_) {
    auto clock_handle = clock_->get_clock_handle();
    rcl_ret_t ret = rcl_disable_ros_time_override(clock_handle);
    if (ret != RCL_RET_OK) {
      throw std::runtime_error("Failed to disable ros_time_override: " + std::to_string(ret));
    }
  }
}

void TimeSource::NodeState::set_clock(const builtin_interfaces::msg::Time & msg_time)
{
  if (!clock_) {
    return;
  }

  auto clock_handle = clock_->get_clock_handle();
  rcl_time_point_value_t time_point =
    static_cast<rcl_time_point_value_t>(RCL_S_TO_NS(msg_time.sec)) + msg_time.nanosec;
  rcl_ret_t ret = rcl_set_ros_time_override(clock_handle, time_point);
  if (ret != RCL_RET_OK) {
    throw std::runtime_error("Failed to set ros_time_override: " + std::to_string(ret));
  }
}

void TimeSource::NodeState::create_clock_subscription()
{
  clock_subscription_ = agnocast_node_->create_subscription<rosgraph_msgs::msg::Clock>(
    "/clock", qos_,
    [this](const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg) { clock_cb(msg); });

  enable_ros_time();
}

void TimeSource::NodeState::destroy_clock_subscription()
{
  if (clock_subscription_) {
    clock_subscription_.reset();
    disable_ros_time();
  }
}

void TimeSource::NodeState::clock_cb(
  const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg)
{
  if (!ros_time_active_) {
    enable_ros_time();
  }
  set_clock(msg->clock);
}

// TimeSource implementation

TimeSource::TimeSource(agnocast::Node * node, const rclcpp::QoS & qos)
: node_state_(std::make_shared<NodeState>(node, qos)), constructed_qos_(qos)
{
}

TimeSource::TimeSource(const rclcpp::QoS & qos) : node_state_(nullptr), constructed_qos_(qos)
{
}

TimeSource::~TimeSource() = default;

void TimeSource::attachNode(agnocast::Node * node)
{
  attachNode(node->get_node_base_interface(), node->get_node_parameters_interface(), node);
}

void TimeSource::attachNode(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_interface,
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_interface,
  agnocast::Node * node)
{
  if (node_state_) {
    detachNode();
  }
  node_state_ = std::make_shared<NodeState>(
    node_base_interface, node_parameters_interface, node, constructed_qos_);
}

void TimeSource::detachNode()
{
  node_state_.reset();
}

void TimeSource::attachClock(rclcpp::Clock::SharedPtr clock)
{
  if (!node_state_) {
    throw std::runtime_error("Cannot attach clock without a node");
  }
  node_state_->attachClock(std::move(clock));
}

void TimeSource::detachClock(rclcpp::Clock::SharedPtr clock)
{
  if (node_state_) {
    node_state_->detachClock(std::move(clock));
  }
}

}  // namespace agnocast

#pragma once

#include "agnocast/node/time_source.hpp"
#include "rclcpp/macros.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_clock_interface.hpp"
#include "rclcpp/node_interfaces/node_parameters_interface.hpp"
#include "rclcpp/node_interfaces/node_time_source_interface.hpp"
#include "rclcpp/qos.hpp"
#include "rclcpp/visibility_control.hpp"

namespace agnocast
{
class Node;
}

namespace agnocast::node_interfaces
{

/// Implementation of the NodeTimeSource part of the Node API.
class NodeTimeSource : public rclcpp::node_interfaces::NodeTimeSourceInterface
{
public:
  RCLCPP_SMART_PTR_ALIASES_ONLY(NodeTimeSource)

  NodeTimeSource(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base,
    rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters,
    rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock, agnocast::Node * node,
    const rclcpp::QoS & qos = rclcpp::ClockQoS(), bool use_clock_thread = true);

  virtual ~NodeTimeSource();

private:
  RCLCPP_DISABLE_COPY(NodeTimeSource)

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_;
  rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock_;

  agnocast::TimeSource time_source_;
};

}  // namespace agnocast::node_interfaces

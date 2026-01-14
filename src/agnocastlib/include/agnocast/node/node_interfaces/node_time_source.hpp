#pragma once

#include "agnocast/node/time_source.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_clock_interface.hpp"
#include "rclcpp/node_interfaces/node_parameters_interface.hpp"
#include "rclcpp/node_interfaces/node_time_source_interface.hpp"
#include "rclcpp/qos.hpp"

namespace agnocast
{
class Node;
}

namespace agnocast::node_interfaces
{

class NodeTimeSource : public rclcpp::node_interfaces::NodeTimeSourceInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTimeSource>;
  using WeakPtr = std::weak_ptr<NodeTimeSource>;

  NodeTimeSource(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base,
    rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters,
    rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock, agnocast::Node * node,
    const rclcpp::QoS & qos = rclcpp::ClockQoS());

  ~NodeTimeSource() override = default;

private:
  agnocast::TimeSource time_source_;
};

}  // namespace agnocast::node_interfaces

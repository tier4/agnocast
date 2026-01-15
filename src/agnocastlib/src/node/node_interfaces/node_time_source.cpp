#include "agnocast/node/node_interfaces/node_time_source.hpp"

#include "agnocast/node/agnocast_node.hpp"

namespace agnocast::node_interfaces
{

NodeTimeSource::NodeTimeSource(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base,
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters,
  rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock, agnocast::Node * node,
  const rclcpp::QoS & qos)
: time_source_(qos)
{
  (void)node_base;
  (void)node_parameters;
  time_source_.attachNode(node);
  time_source_.attachClock(node_clock->get_clock());
}

}  // namespace agnocast::node_interfaces

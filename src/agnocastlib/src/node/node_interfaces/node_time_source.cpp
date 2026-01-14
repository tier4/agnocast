#include "agnocast/node/node_interfaces/node_time_source.hpp"

#include <memory>
#include <string>

using agnocast::node_interfaces::NodeTimeSource;

NodeTimeSource::NodeTimeSource(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base,
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters,
  rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock, agnocast::Node * node,
  const rclcpp::QoS & qos, bool use_clock_thread)
: node_base_(node_base),
  node_parameters_(node_parameters),
  node_clock_(node_clock),
  time_source_(qos, use_clock_thread)
{
  time_source_.attachNode(node_base_, node_parameters_, node_clock_, node);
  if (node_clock_) {
    time_source_.attachClock(node_clock_->get_clock());
  }
}

NodeTimeSource::~NodeTimeSource()
{
}

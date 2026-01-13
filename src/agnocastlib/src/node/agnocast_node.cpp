#include "agnocast/node/agnocast_node.hpp"

#include "agnocast/node/agnocast_arguments.hpp"
#include "agnocast/node/agnocast_context.hpp"

#include <rcl/time.h>

namespace agnocast
{

Node::Node(const std::string & node_name, const rclcpp::NodeOptions & options)
: Node(node_name, "", options)
{
}

Node::Node(
  const std::string & node_name, const std::string & namespace_,
  const rclcpp::NodeOptions & options)
: local_args_(parse_arguments(options.arguments()))
{
  node_base_ = std::make_shared<node_interfaces::NodeBase>(
    node_name, namespace_, options.context(), local_args_.get(), options.use_intra_process_comms(),
    options.enable_topic_statistics());
  logger_ = rclcpp::get_logger(node_base_->get_name());

  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(
    node_base_, options.parameter_overrides(), local_args_.get());

  node_clock_ = std::make_shared<node_interfaces::NodeClock>(RCL_ROS_TIME);

  // Initialize NodeTimeSource for simulation time support
  bool use_sim_time = false;
  if (node_parameters_->has_parameter("use_sim_time")) {
    use_sim_time = node_parameters_->get_parameter("use_sim_time").as_bool();
  } else {
    // Declare use_sim_time parameter with default value false
    node_parameters_->declare_parameter(
      "use_sim_time", rclcpp::ParameterValue(false), rcl_interfaces::msg::ParameterDescriptor{},
      false);
  }

  node_time_source_ = std::make_shared<node_interfaces::NodeTimeSource>(
    node_clock_->get_clock(), use_sim_time, node_topics_, options.clock_qos());
}

}  // namespace agnocast

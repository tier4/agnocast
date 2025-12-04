#include "agnocast/agnocast_node.hpp"

#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Node::Node(const std::string & node_name, const rclcpp::NodeOptions & options)
{
  initialize_node(node_name, "", options.context());
}

Node::Node(
  const std::string & node_name, const std::string & namespace_,
  const rclcpp::NodeOptions & options)
{
  initialize_node(node_name, namespace_, options.context());
}

void Node::initialize_node(
  const std::string & node_name, const std::string & ns, rclcpp::Context::SharedPtr context)
{
  node_base_ = std::make_shared<node_interfaces::NodeBase>(node_name, ns, context);
  logger_ = rclcpp::get_logger(node_base_->get_name());
}

}  // namespace agnocast

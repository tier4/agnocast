#include "agnocast/agnocast_node.hpp"

#include "agnocast/agnocast_arguments.hpp"
#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Node::Node(const std::string & node_name, const rclcpp::NodeOptions & options)
: Node(node_name, "", options)
{
}

Node::Node(
  const std::string & node_name, const std::string & namespace_,
  const rclcpp::NodeOptions & options)
{
  // Parse local arguments from NodeOptions::arguments()
  auto local_args = parse_arguments(options.arguments());

  // Create NodeBase with local remap rules
  // Global remap rules are retrieved from context inside NodeBase constructor
  node_base_ = std::make_shared<node_interfaces::NodeBase>(
    node_name, namespace_, options.context(), std::move(local_args.remap_rules),
    options.use_intra_process_comms(), options.enable_topic_statistics());
  logger_ = rclcpp::get_logger(node_base_->get_name());

  // NodeTopics accesses remap rules via node_base_
  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(
    node_base_, options.parameter_overrides(), local_args);
}

}  // namespace agnocast

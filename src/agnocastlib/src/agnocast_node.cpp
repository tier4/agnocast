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
  node_base_ = std::make_shared<node_interfaces::NodeBase>(
    node_name, namespace_, options.context(), options.use_intra_process_comms(),
    options.enable_topic_statistics());
  logger_ = rclcpp::get_logger(node_base_->get_name());

  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  auto local_args = parse_arguments(options.arguments());

  // Get global arguments from context and apply remapping
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    if (g_context.is_initialized()) {
      node_topics_->set_global_arguments(g_context.get_remap_rules());
    }
  }

  // Apply local remap rules from NodeOptions::arguments()
  node_topics_->set_local_arguments(std::move(local_args.remap_rules));

  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(
    node_base_, options.parameter_overrides(), local_args);
}

}  // namespace agnocast

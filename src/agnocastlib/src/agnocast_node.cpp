#include "agnocast/agnocast_node.hpp"

#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Node::Node(const std::string & node_name, const rclcpp::NodeOptions & options)
{
  initialize_node(node_name, "", options);
}

Node::Node(
  const std::string & node_name, const std::string & namespace_,
  const rclcpp::NodeOptions & options)
{
  initialize_node(node_name, namespace_, options);
}

void Node::initialize_node(
  const std::string & node_name, const std::string & ns, const rclcpp::NodeOptions & options)
{
  node_base_ = std::make_shared<node_interfaces::NodeBase>(
    node_name, ns, options.context(), options.enable_topic_statistics());
  logger_ = rclcpp::get_logger(node_base_->get_name());

  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  // Collect parameter overrides from agnocast::Context and NodeOptions
  std::vector<rclcpp::Parameter> parameter_overrides;
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    if (g_context.is_initialized()) {
      auto node_params = g_context.get_param_overrides(get_fully_qualified_name());
      for (const auto & [name, value] : node_params) {
        parameter_overrides.emplace_back(name, value);
      }
    }
  }
  for (const auto & param : options.parameter_overrides()) {
    parameter_overrides.push_back(param);
  }

  node_parameters_ =
    std::make_shared<node_interfaces::NodeParameters>(node_base_, parameter_overrides);
}

}  // namespace agnocast

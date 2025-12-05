#include "agnocast/agnocast_node.hpp"

#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Node::Node(const std::string & node_name, const rclcpp::NodeOptions & options)
{
  initialize_node(node_name, "", options.context());

  // Apply parameter overrides from NodeOptions (takes precedence over global context)
  for (const auto & param : options.parameter_overrides()) {
    node_parameters_->add_parameter_override(param.get_name(), param.get_parameter_value());
  }
}

Node::Node(
  const std::string & node_name, const std::string & namespace_,
  const rclcpp::NodeOptions & options)
{
  initialize_node(node_name, namespace_, options.context());

  // Apply parameter overrides from NodeOptions (takes precedence over global context)
  for (const auto & param : options.parameter_overrides()) {
    node_parameters_->add_parameter_override(param.get_name(), param.get_parameter_value());
  }
}

void Node::initialize_node(
  const std::string & node_name, const std::string & ns, rclcpp::Context::SharedPtr context)
{
  // Create NodeBase first - it will apply node name/namespace remapping internally
  // Corresponds to rclcpp::NodeBase constructor calling rcl_node_init
  // which calls rcl_remap_node_name and rcl_remap_node_namespace
  if (context) {
    node_base_ = std::make_shared<node_interfaces::NodeBase>(node_name, ns, context);
  } else {
    node_base_ = std::make_shared<node_interfaces::NodeBase>(node_name, ns);
  }

  // Update logger with actual node name
  logger_ = rclcpp::get_logger(node_base_->get_name());

  // Create NodeTopics with the (already remapped) NodeBase
  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  // Set NodeTopics back-reference in NodeBase for resolve_topic_or_service_name
  node_base_->set_node_topics(node_topics_);

  // Create NodeParameters with NodeBase
  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(node_base_);

  // Apply global context for topic remapping and parameter overrides
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    auto & global_ctx = Context::instance();
    if (global_ctx.is_initialized()) {
      // Add topic remap rules to NodeTopics
      auto global_rules = global_ctx.get_remap_rules();
      for (const auto & rule : global_rules) {
        if (rule.type == RemapType::TOPIC_OR_SERVICE) {
          node_topics_->add_remap_rule(rule);
        }
      }

      // Get parameter overrides for this specific node (YAML + global overrides)
      // Corresponds to rcl_arguments_get_param_overrides in rcl/src/rcl/arguments.c
      auto node_params = global_ctx.get_param_overrides(get_fully_qualified_name());
      for (const auto & [name, value] : node_params) {
        node_parameters_->add_parameter_override(name, value);
      }
    }
  }
}

const Node::ParameterValue & Node::declare_parameter(
  const std::string & name, const ParameterValue & default_value,
  const ParameterDescriptor & descriptor, bool ignore_override)
{
  return node_parameters_->declare_parameter(name, default_value, descriptor, ignore_override);
}

}  // namespace agnocast

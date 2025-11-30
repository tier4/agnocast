#include "agnocast/agnocast_node.hpp"
#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Node::Node(const std::string & node_name, const std::string & ns)
{
  // Create NodeBase first - it will apply node name/namespace remapping internally
  // Corresponds to rclcpp::NodeBase constructor calling rcl_node_init
  // which calls rcl_remap_node_name and rcl_remap_node_namespace
  node_base_ = std::make_shared<node_interfaces::NodeBase>(node_name, ns);

  // Create NodeTopics with the (already remapped) NodeBase
  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  // Create NodeParameters with NodeBase
  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(node_base_);

  // Apply global context for topic remapping and parameter overrides
  auto & global_ctx = GlobalContext::instance();
  if (global_ctx.is_initialized()) {
    // Add topic remap rules to NodeTopics
    auto global_rules = global_ctx.get_remap_rules();
    for (const auto & rule : global_rules) {
      if (rule.type == RemapType::TOPIC) {
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

const Node::ParameterValue & Node::declare_parameter(
  const std::string & name,
  const ParameterValue & default_value,
  const ParameterDescriptor & descriptor,
  bool ignore_override)
{
  // Declare parameter using NodeParameters interface
  node_parameters_->declare_parameter(
    name,
    default_value,
    descriptor.description,
    descriptor.read_only);

  // Return the parameter value from the internal storage
  // This is a bit awkward due to the interface design, but maintains backward compatibility
  // We need to access the internal parameter storage through get_parameter
  static thread_local ParameterValue return_value;

  if (std::holds_alternative<bool>(default_value)) {
    bool v;
    node_parameters_->get_parameter(name, v);
    return_value = v;
  } else if (std::holds_alternative<int64_t>(default_value)) {
    int64_t v;
    node_parameters_->get_parameter(name, v);
    return_value = v;
  } else if (std::holds_alternative<double>(default_value)) {
    double v;
    node_parameters_->get_parameter(name, v);
    return_value = v;
  } else if (std::holds_alternative<std::string>(default_value)) {
    std::string v;
    node_parameters_->get_parameter(name, v);
    return_value = v;
  }

  return return_value;
}

}  // namespace agnocast

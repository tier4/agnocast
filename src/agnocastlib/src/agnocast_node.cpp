#include "agnocast/agnocast_node.hpp"

#include "agnocast/agnocast_context.hpp"
#include "rclcpp/contexts/default_context.hpp"

namespace agnocast
{

namespace
{
std::string query_node_name_from_context()
{
  auto & ctx = Context::instance();
  if (ctx.is_initialized()) {
    // Look for __node or __name remapping
    for (const auto & rule : ctx.get_remap_rules()) {
      if (rule.type == RemapType::NODENAME) {
        return rule.replacement;
      }
    }
  }
  return "agnocast_node";  // Default name if not specified
}

// Extract node name from NodeOptions arguments
// Looks for patterns like: --ros-args -r __node:=name or __name:=name
std::string extract_node_name_from_options(const rclcpp::NodeOptions & options)
{
  const auto & args = options.arguments();
  for (size_t i = 0; i < args.size(); ++i) {
    if (args[i] == "-r" || args[i] == "--remap") {
      if (i + 1 < args.size()) {
        const auto & remap = args[i + 1];
        if (remap.find("__node:=") == 0) {
          return remap.substr(8);  // Length of "__node:="
        }
        if (remap.find("__name:=") == 0) {
          return remap.substr(8);  // Length of "__name:="
        }
      }
    }
    // Also check for direct __node:= without -r flag (component_container style)
    if (args[i].find("__node:=") == 0) {
      return args[i].substr(8);
    }
    if (args[i].find("__name:=") == 0) {
      return args[i].substr(8);
    }
  }
  return "agnocast_node";  // Default name if not specified
}

// Extract namespace from NodeOptions arguments
// Looks for patterns like: --ros-args -r __ns:=namespace
std::string extract_namespace_from_options(const rclcpp::NodeOptions & options)
{
  const auto & args = options.arguments();
  for (size_t i = 0; i < args.size(); ++i) {
    if (args[i] == "-r" || args[i] == "--remap") {
      if (i + 1 < args.size()) {
        const auto & remap = args[i + 1];
        if (remap.find("__ns:=") == 0) {
          return remap.substr(6);  // Length of "__ns:="
        }
      }
    }
    // Also check for direct __ns:= without -r flag
    if (args[i].find("__ns:=") == 0) {
      return args[i].substr(6);
    }
  }
  return "";  // Default to empty namespace
}

}  // namespace

Node::Node()
{
  initialize_node(query_node_name_from_context(), "");
}

Node::Node(const std::string & node_name, const std::string & ns)
{
  initialize_node(node_name, ns);
}

Node::Node(const rclcpp::NodeOptions & options)
{
  std::string node_name = extract_node_name_from_options(options);
  std::string ns = extract_namespace_from_options(options);
  auto context = options.context();

  // Create NodeBase with explicit context (for Composable Node support)
  node_base_ = std::make_shared<node_interfaces::NodeBase>(node_name, ns, context);

  // Update logger with actual node name
  logger_ = rclcpp::get_logger(node_base_->get_name());

  // Create NodeTopics with the (already remapped) NodeBase
  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  // Set NodeTopics back-reference in NodeBase for resolve_topic_or_service_name
  node_base_->set_node_topics(node_topics_);

  // Create NodeParameters with NodeBase
  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(node_base_);

  // Apply global context for topic remapping (from agnocast::init)
  auto & global_ctx = Context::instance();
  if (global_ctx.is_initialized()) {
    // Add topic remap rules to NodeTopics
    auto global_rules = global_ctx.get_remap_rules();
    for (const auto & rule : global_rules) {
      if (rule.type == RemapType::TOPIC) {
        node_topics_->add_remap_rule(rule);
      }
    }

    // Get parameter overrides from agnocast::Context (YAML + global overrides)
    auto node_params = global_ctx.get_param_overrides(node_base_->get_fully_qualified_name());
    for (const auto & [name, value] : node_params) {
      node_parameters_->add_parameter_override(name, value);
    }
  }

  // Apply parameter overrides from NodeOptions (takes precedence over global context)
  for (const auto & param : options.parameter_overrides()) {
    switch (param.get_type()) {
      case rclcpp::ParameterType::PARAMETER_BOOL:
        node_parameters_->add_parameter_override(param.get_name(), param.as_bool());
        break;
      case rclcpp::ParameterType::PARAMETER_INTEGER:
        node_parameters_->add_parameter_override(param.get_name(), param.as_int());
        break;
      case rclcpp::ParameterType::PARAMETER_DOUBLE:
        node_parameters_->add_parameter_override(param.get_name(), param.as_double());
        break;
      case rclcpp::ParameterType::PARAMETER_STRING:
        node_parameters_->add_parameter_override(param.get_name(), param.as_string());
        break;
      default:
        // Unsupported parameter types are silently ignored
        break;
    }
  }
}

void Node::initialize_node(const std::string & node_name, const std::string & ns)
{
  // Create NodeBase first - it will apply node name/namespace remapping internally
  // Corresponds to rclcpp::NodeBase constructor calling rcl_node_init
  // which calls rcl_remap_node_name and rcl_remap_node_namespace
  node_base_ = std::make_shared<node_interfaces::NodeBase>(node_name, ns);

  // Update logger with actual node name
  logger_ = rclcpp::get_logger(node_base_->get_name());

  // Create NodeTopics with the (already remapped) NodeBase
  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  // Set NodeTopics back-reference in NodeBase for resolve_topic_or_service_name
  node_base_->set_node_topics(node_topics_);

  // Create NodeParameters with NodeBase
  node_parameters_ = std::make_shared<node_interfaces::NodeParameters>(node_base_);

  // Apply global context for topic remapping and parameter overrides
  auto & global_ctx = Context::instance();
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
  const std::string & name, const ParameterValue & default_value,
  const ParameterDescriptor & descriptor, bool ignore_override)
{
  // Declare parameter using NodeParameters interface (agnocast-specific method)
  node_parameters_->declare_parameter_simple(
    name, default_value, descriptor.description, descriptor.read_only, ignore_override);

  // Return the parameter value from the internal storage
  // Use rclcpp API to get the parameter and convert to agnocast ParameterValue
  static thread_local ParameterValue return_value;

  rclcpp::Parameter param;
  if (node_parameters_->get_parameter(name, param)) {
    switch (param.get_type()) {
      case rclcpp::ParameterType::PARAMETER_BOOL:
        return_value = param.as_bool();
        break;
      case rclcpp::ParameterType::PARAMETER_INTEGER:
        return_value = param.as_int();
        break;
      case rclcpp::ParameterType::PARAMETER_DOUBLE:
        return_value = param.as_double();
        break;
      case rclcpp::ParameterType::PARAMETER_STRING:
        return_value = param.as_string();
        break;
      default:
        return_value = default_value;
        break;
    }
  } else {
    return_value = default_value;
  }

  return return_value;
}

}  // namespace agnocast

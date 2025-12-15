#include "agnocast/agnocast_node.hpp"

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
    node_name, namespace_, options.context(), options.enable_topic_statistics());
  logger_ = rclcpp::get_logger(node_base_->get_name());

  node_topics_ = std::make_shared<node_interfaces::NodeTopics>(node_base_);

  // Set NodeTopics back-reference in NodeBase for resolve_topic_or_service_name
  node_base_->set_node_topics(node_topics_);

  // Apply global context for topic remapping
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    if (g_context.is_initialized()) {
      node_topics_->set_global_arguments(g_context.get_remap_rules());
    }
  }

  node_parameters_ =
    std::make_shared<node_interfaces::NodeParameters>(node_base_, options.parameter_overrides());

  // Apply remap rules from NodeOptions::arguments() (from launch file <remap> tags)
  apply_remap_rules_from_arguments(options.arguments());
}

const Node::ParameterValue & Node::declare_parameter(
  const std::string & name, const ParameterValue & default_value,
  const ParameterDescriptor & descriptor, bool ignore_override)
{
  return node_parameters_->declare_parameter(name, default_value, descriptor, ignore_override);
}

void Node::apply_remap_rules_from_arguments(const std::vector<std::string> & arguments)
{
  // Parse remap rules from NodeOptions::arguments()
  // Format: --ros-args -r from:=to -r from2:=to2 ...
  std::vector<RemapRule> local_rules;
  bool parsing_ros_args = false;
  for (size_t i = 0; i < arguments.size(); ++i) {
    const std::string & arg = arguments[i];

    if (arg == "--ros-args") {
      parsing_ros_args = true;
      continue;
    }

    if (arg == "--") {
      parsing_ros_args = false;
      continue;
    }

    if (parsing_ros_args && (arg == "-r" || arg == "--remap") && i + 1 < arguments.size()) {
      ++i;
      const std::string & remap_arg = arguments[i];

      // Parse remap rule: from:=to
      size_t separator = remap_arg.find(":=");
      if (separator == std::string::npos) {
        continue;
      }

      std::string from = remap_arg.substr(0, separator);
      std::string to = remap_arg.substr(separator + 2);

      RemapRule rule;
      rule.type = RemapType::TOPIC_OR_SERVICE;
      rule.match = from;
      rule.replacement = to;

      local_rules.push_back(rule);
    }
  }
  node_topics_->set_local_arguments(std::move(local_rules));
}

}  // namespace agnocast

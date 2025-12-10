#include "agnocast/node_interfaces/node_topics.hpp"

#include <stdexcept>
#include <utility>

namespace agnocast::node_interfaces
{

NodeTopics::NodeTopics(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base)
: node_base_(std::move(node_base))
{
}

std::string NodeTopics::resolve_topic_name(const std::string & name, bool only_expand) const
{
  // Corresponds to rcl_node_resolve_name in rcl/src/rcl/node_resolve_name.c:134-162

  if (only_expand) {
    return expand_topic_name(name);
  }

  // TODO(Koichi98)
  return "";
}

rclcpp::node_interfaces::NodeBaseInterface * NodeTopics::get_node_base_interface() const
{
  return node_base_.get();
}

rclcpp::PublisherBase::SharedPtr NodeTopics::create_publisher(
  const std::string & topic_name, const rclcpp::PublisherFactory & publisher_factory,
  const rclcpp::QoS & qos)
{
  (void)topic_name;
  (void)publisher_factory;
  (void)qos;
  throw std::runtime_error(
    "NodeTopics::create_publisher is not supported in agnocast. "
    "Use agnocast::create_publisher instead.");
}

void NodeTopics::add_publisher(
  rclcpp::PublisherBase::SharedPtr publisher, rclcpp::CallbackGroup::SharedPtr callback_group)
{
  (void)publisher;
  (void)callback_group;
  throw std::runtime_error(
    "NodeTopics::add_publisher is not supported in agnocast. "
    "Use agnocast::create_publisher instead.");
}

rclcpp::SubscriptionBase::SharedPtr NodeTopics::create_subscription(
  const std::string & topic_name, const rclcpp::SubscriptionFactory & subscription_factory,
  const rclcpp::QoS & qos)
{
  (void)topic_name;
  (void)subscription_factory;
  (void)qos;
  throw std::runtime_error(
    "NodeTopics::create_subscription is not supported in agnocast. "
    "Use agnocast::create_subscription instead.");
}

void NodeTopics::add_subscription(
  rclcpp::SubscriptionBase::SharedPtr subscription, rclcpp::CallbackGroup::SharedPtr callback_group)
{
  (void)subscription;
  (void)callback_group;
  throw std::runtime_error(
    "NodeTopics::add_subscription is not supported in agnocast. "
    "Use agnocast::create_subscription instead.");
}

rclcpp::node_interfaces::NodeTimersInterface * NodeTopics::get_node_timers_interface() const
{
  throw std::runtime_error(
    "NodeTopics::get_node_timers_interface is not supported in agnocast. "
    "Timers interface is not available.");
}

std::string NodeTopics::expand_topic_name(const std::string & input_topic_name) const
{
  // Corresponds to rcl_expand_topic_name in rcl/src/rcl/expand_topic_name.c:44-219
  // Handles:
  // - Private topics: "~foo" -> "/namespace/node_name/foo"
  // - Substitutions: "{node}" -> node_name, "{ns}" or "{namespace}" -> namespace
  // - Relative topics: "foo" -> "/namespace/foo"
  // - Absolute topics: "/foo" -> "/foo" (unchanged)

  if (input_topic_name.empty()) {
    return input_topic_name;
  }

  std::string local_output = input_topic_name;
  std::string node_name = node_base_->get_name();
  std::string namespace_ = node_base_->get_namespace();

  // Check for substitutions in the topic name
  bool has_a_substitution = input_topic_name.find('{') != std::string::npos;
  bool has_a_namespace_tilde = !input_topic_name.empty() && input_topic_name[0] == '~';
  bool is_absolute = !input_topic_name.empty() && input_topic_name[0] == '/';

  // If absolute and no substitution, return as-is
  if (is_absolute && !has_a_substitution) {
    return input_topic_name;
  }

  // Handle private topic name (starts with '~')
  // Replace ~ with namespace/node_name
  if (has_a_namespace_tilde) {
    if (namespace_.empty() || namespace_ == std::string("/")) {
      local_output = "/" + node_name + input_topic_name.substr(1);
    } else {
      local_output = namespace_ + "/" + node_name + input_topic_name.substr(1);
    }
  }

  // Handle substitutions ({node}, {ns}, {namespace})
  if (has_a_substitution) {
    size_t pos = 0;
    while ((pos = local_output.find('{', pos)) != std::string::npos) {
      size_t end_pos = local_output.find('}', pos);
      if (end_pos == std::string::npos) {
        break;  // Malformed substitution
      }

      std::string substitution = local_output.substr(pos, end_pos - pos + 1);
      std::string replacement;

      if (substitution == "{node}") {
        replacement = node_name;
      } else if (substitution == "{ns}" || substitution == "{namespace}") {
        replacement = namespace_;
      }
      // Unknown substitutions are left as-is

      if (!replacement.empty()) {
        local_output.replace(pos, substitution.length(), replacement);
        pos += replacement.length();
      } else {
        pos = end_pos + 1;
      }
    }
  }

  // Make relative topic names absolute by prepending namespace
  if (!local_output.empty() && local_output[0] != '/') {
    if (namespace_.empty() || namespace_ == std::string("/")) {
      local_output = "/" + local_output;
    } else {
      local_output = namespace_ + "/" + local_output;
    }
  }

  return local_output;
}

}  // namespace agnocast::node_interfaces

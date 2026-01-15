#include "agnocast/node/node_interfaces/node_topics.hpp"

#include <stdexcept>
#include <utility>

namespace agnocast::node_interfaces
{

NodeTopics::NodeTopics(NodeBase::SharedPtr node_base) : node_base_(std::move(node_base))
{
}

std::string NodeTopics::resolve_topic_name(const std::string & name, bool only_expand) const
{
  return node_base_->resolve_topic_or_service_name(name, false, only_expand);
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
  // TODO(agnocast): This method is called by rclcpp's internal create_timer() helpers.
  // For now, we throw because agnocast::Node provides get_node_timers_interface() directly.
  // If needed, NodeTopics could store a reference to NodeTimers and return it here.
  throw std::runtime_error(
    "NodeTopics::get_node_timers_interface is not implemented. "
    "Use agnocast::Node::get_node_timers_interface() instead.");
}

}  // namespace agnocast::node_interfaces

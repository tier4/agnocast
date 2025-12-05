#ifndef AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_

#include "agnocast/agnocast_context.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_topics_interface.hpp"

#include <memory>
#include <string>
#include <vector>

namespace agnocast::namespace node_interfaces
{

class NodeTopics : public rclcpp::node_interfaces::NodeTopicsInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTopics>;
  using WeakPtr = std::weak_ptr<NodeTopics>;

  explicit NodeTopics(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base);

  virtual ~NodeTopics() = default;

  std::string resolve_topic_name(const std::string & name, bool only_expand = false) const override;
  rclcpp::node_interfaces::NodeBaseInterface * get_node_base_interface() const override;

  // ===== Not supported methods (throw runtime_error) =====
  rclcpp::PublisherBase::SharedPtr create_publisher(
    const std::string & topic_name, const rclcpp::PublisherFactory & publisher_factory,
    const rclcpp::QoS & qos) override;
  void add_publisher(
    rclcpp::PublisherBase::SharedPtr publisher,
    rclcpp::CallbackGroup::SharedPtr callback_group) override;
  rclcpp::SubscriptionBase::SharedPtr create_subscription(
    const std::string & topic_name, const rclcpp::SubscriptionFactory & subscription_factory,
    const rclcpp::QoS & qos) override;
  void add_subscription(
    rclcpp::SubscriptionBase::SharedPtr subscription,
    rclcpp::CallbackGroup::SharedPtr callback_group) override;
  rclcpp::node_interfaces::NodeTimersInterface * get_node_timers_interface() const override;

private:
  std::string resolve_name(const std::string & input_topic_name) const;
  std::string expand_topic_name(const std::string & input_topic_name) const;
  std::string remap_name(const std::string & name) const;
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  std::vector<RemapRule> remap_rules_;  // Only TOPIC type rules
};
}  // namespace agnocast::node_interfaces

#endif  // AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_

#ifndef AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_

#include "agnocast/agnocast_context.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_topics_interface.hpp"

#include <memory>
#include <string>
#include <vector>

namespace agnocast
{
namespace node_interfaces
{

/// Implementation of the NodeTopics part of the Node API.
/// Inherits from rclcpp::node_interfaces::NodeTopicsInterface for compatibility.
class NodeTopics : public rclcpp::node_interfaces::NodeTopicsInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTopics>;
  using WeakPtr = std::weak_ptr<NodeTopics>;

  /**
   * @brief Construct a NodeTopics.
   *
   * @param node_base Pointer to the node base interface
   */
  explicit NodeTopics(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base);

  virtual ~NodeTopics() = default;

  // ===== Implemented methods =====

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

  // ===== Internal helper methods (for rclcpp API implementation) =====

  /**
   * @brief Add a remap rule for topic remapping.
   * @note Internal helper for command-line argument processing.
   *
   * @param rule Remap rule to add
   */
  void add_remap_rule(const RemapRule & rule);

private:
  /**
   * @brief Resolve a name (main implementation).
   *
   * Calls expand_topic_name then remap_name.
   * Corresponds to rcl_resolve_name in rcl/src/rcl/node_resolve_name.c.
   *
   * @param input_topic_name Topic name to resolve
   * @return Resolved topic name
   */
  std::string resolve_name(const std::string & input_topic_name) const;

  /**
   * @brief Expand a topic name (handle substitutions, private/relative/absolute).
   *
   * Corresponds to rcl_expand_topic_name in rcl/src/rcl/expand_topic_name.c.
   *
   * @param input_topic_name Topic name to expand
   * @return Expanded topic name
   */
  std::string expand_topic_name(const std::string & input_topic_name) const;

  /**
   * @brief Apply remapping to a topic name.
   *
   * Corresponds to rcl_remap_name in rcl/src/rcl/remap.c.
   *
   * @param name Name to remap
   * @return Remapped name (or original if no remapping exists)
   */
  std::string remap_name(const std::string & name) const;

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  std::vector<RemapRule> remap_rules_;  // Only TOPIC type rules
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_

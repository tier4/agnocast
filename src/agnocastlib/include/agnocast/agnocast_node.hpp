#include "agnocast/agnocast_context.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "agnocast/node_interfaces/node_base.hpp"
#include "agnocast/node_interfaces/node_topics.hpp"

#include <algorithm>
#include <memory>
#include <string>

namespace agnocast
{

class Node
{
public:
  using SharedPtr = std::shared_ptr<Node>;

  explicit Node(
    const std::string & node_name, const rclcpp::NodeOptions & options = rclcpp::NodeOptions());

  explicit Node(
    const std::string & node_name, const std::string & namespace_,
    const rclcpp::NodeOptions & options = rclcpp::NodeOptions());

  std::string get_name() const { return node_base_->get_name(); }
  rclcpp::Logger get_logger() const { return logger_; }
  std::string get_namespace() const { return node_base_->get_namespace(); }
  std::string get_fully_qualified_name() const { return node_base_->get_fully_qualified_name(); }

  rclcpp::CallbackGroup::SharedPtr get_default_callback_group()
  {
    return node_base_->get_default_callback_group();
  }

  rclcpp::CallbackGroup::SharedPtr create_callback_group(
    rclcpp::CallbackGroupType group_type, bool automatically_add_to_executor_with_node = true)
  {
    return node_base_->create_callback_group(group_type, automatically_add_to_executor_with_node);
  }

  bool callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & callback_group)
  {
    return node_base_->callback_group_in_node(callback_group);
  }

  // Non-const to align with rclcpp::Node API
  // cppcheck-suppress functionConst
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr get_node_base_interface()
  {
    return node_base_;
  }

  // Non-const to align with rclcpp::Node API
  // cppcheck-suppress functionConst
  rclcpp::node_interfaces::NodeTopicsInterface::SharedPtr get_node_topics_interface()
  {
    return node_topics_;
  }

  template <typename MessageT, typename Func>
  typename agnocast::Subscription<MessageT>::SharedPtr create_subscription(
    const std::string & topic_name, size_t queue_size, Func && callback,
    agnocast::SubscriptionOptions options)
  {
    return std::make_shared<Subscription<MessageT>>(
      this, topic_name, rclcpp::QoS(rclcpp::KeepLast(queue_size)), std::forward<Func>(callback),
      options);
  }

private:
  void initialize_node(
    const std::string & node_name, const std::string & ns, const rclcpp::NodeOptions & options);

  rclcpp::Logger logger_{rclcpp::get_logger("agnocast_node")};
  node_interfaces::NodeBase::SharedPtr node_base_;
  node_interfaces::NodeTopics::SharedPtr node_topics_;
};

}  // namespace agnocast

#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_node.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

#include <iostream>

using std::placeholders::_1;

// Composable node (uses rclcpp::Node for component infrastructure)
class MinimalSubscriberComponent : public rclcpp::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Node::SharedPtr agnocast_node_;
  std::string topic_name_;

  void callback(
    const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(this->get_logger(), "subscribe message: id=%ld", message->id);
  }

public:
  explicit MinimalSubscriberComponent(const rclcpp::NodeOptions & options)
  : Node("minimal_subscriber", options)
  {
    agnocast_node_ = std::make_shared<agnocast::Node>("minimal_subscriber");
    agnocast_node_->declare_parameter("topic_name", std::string("my_topic"));
    agnocast_node_->get_parameter("topic_name", topic_name_);
    std::string resolved_topic = agnocast_node_->resolve_topic_name(topic_name_);

    RCLCPP_INFO(this->get_logger(), "=== Agnocast Node Parameters ===");
    RCLCPP_INFO(this->get_logger(), "Node name: %s", agnocast_node_->get_name().c_str());
    RCLCPP_INFO(this->get_logger(), "Topic name (resolved): %s", resolved_topic.c_str());
    RCLCPP_INFO(this->get_logger(), "================================");

    rclcpp::CallbackGroup::SharedPtr group =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    sub_dynamic_ = agnocast::create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      this, resolved_topic, 1, std::bind(&MinimalSubscriberComponent::callback, this, _1),
      agnocast_options);
  }
};

// Standalone subscriber (pure agnocast, no rclcpp::Node dependency)
class MinimalSubscriber
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Node::SharedPtr node_;
  std::string topic_name_;

  void callback(
    const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & message)
  {
    std::cout << "[MinimalSubscriber] subscribe message: id=" << message->id << std::endl;
  }

public:
  MinimalSubscriber()
  {
    // Create agnocast::Node (no rclcpp::init required!)
    node_ = std::make_shared<agnocast::Node>("minimal_subscriber");

    // Declare and get parameters
    node_->declare_parameter("topic_name", std::string("my_topic"));
    node_->get_parameter("topic_name", topic_name_);

    // Resolve topic name
    std::string resolved_topic = node_->resolve_topic_name(topic_name_);

    // Log parameter values
    std::cout << "=== Agnocast Node Parameters ===" << std::endl;
    std::cout << "Node name: " << node_->get_name() << std::endl;
    std::cout << "Namespace: " << node_->get_namespace() << std::endl;
    std::cout << "Fully qualified name: " << node_->get_fully_qualified_name() << std::endl;
    std::cout << "Topic name (input): " << topic_name_ << std::endl;
    std::cout << "Topic name (resolved): " << resolved_topic << std::endl;
    std::cout << "================================" << std::endl;

    // Create subscription using agnocast::Node (no rclcpp::Node needed!)
    agnocast::SubscriptionOptions options;
    sub_dynamic_ = agnocast::create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      node_.get(), resolved_topic, 1, std::bind(&MinimalSubscriber::callback, this, _1),
      options);
  }

  agnocast::Node::SharedPtr get_node() { return node_; }
};

// Component registration (only for component builds)
#ifdef BUILD_LISTENER_COMPONENT_ONLY
#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(MinimalSubscriberComponent)
#endif

// Standalone executable main function (pure agnocast, rclcpp::init not required!)
#ifndef BUILD_LISTENER_COMPONENT_ONLY
int main(int argc, char * argv[])
{
  // Initialize agnocast global context only (no rclcpp::init needed!)
  agnocast::init(argc, argv);

  // Note: Executor directly uses CallbackGroups, so rclcpp::init is NOT needed
  agnocast::SingleThreadedAgnocastExecutor executor;
  auto subscriber = std::make_shared<MinimalSubscriber>();

  // Executor doesn't need NodeBaseInterface when using agnocast::Node
  // The subscription's callback group is already registered
  executor.spin();

  return 0;
}
#endif

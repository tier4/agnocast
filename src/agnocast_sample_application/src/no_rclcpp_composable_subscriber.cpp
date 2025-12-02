#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp_components/register_node_macro.hpp"

#include <iostream>

using std::placeholders::_1;

class NoRclcppComposableSubscriber : public agnocast::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;

  void callback(
    const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(
      get_logger(), "I heard dynamic size array message with size: %zu", message->data.size());
  }

public:
  explicit NoRclcppComposableSubscriber(const rclcpp::NodeOptions & options)
  : agnocast::Node(options)
  {
    // Declare parameters with default values
    declare_parameter("topic_name", std::string("my_topic"));
    declare_parameter("queue_size", int64_t(1));

    // Get parameter values
    std::string topic_name;
    int64_t queue_size;
    get_parameter("topic_name", topic_name);
    get_parameter("queue_size", queue_size);

    // Resolve topic name (handles remapping and namespace)
    std::string resolved_topic = resolve_topic_name(topic_name);

    // Log node info and parameters
    RCLCPP_INFO(get_logger(), "=== NoRclcppComposableSubscriber Node Info ===");
    RCLCPP_INFO(get_logger(), "Node name: %s", get_name().c_str());
    RCLCPP_INFO(get_logger(), "Namespace: %s", get_namespace().c_str());
    RCLCPP_INFO(get_logger(), "Fully qualified name: %s", get_fully_qualified_name().c_str());
    RCLCPP_INFO(get_logger(), "Topic name (input): %s", topic_name.c_str());
    RCLCPP_INFO(get_logger(), "Topic name (resolved): %s", resolved_topic.c_str());
    RCLCPP_INFO(get_logger(), "Queue size: %ld", queue_size);
    RCLCPP_INFO(get_logger(), "==============================================");

    auto group = create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    sub_dynamic_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      resolved_topic, static_cast<size_t>(queue_size),
      std::bind(&NoRclcppComposableSubscriber::callback, this, _1), agnocast_options);
  }
};

RCLCPP_COMPONENTS_REGISTER_NODE(NoRclcppComposableSubscriber)

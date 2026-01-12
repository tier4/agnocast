#include <agnocast/agnocast.hpp>

#include <std_msgs/msg/string.hpp>

#include <memory>

// Test subscriber node using agnocast::Node
// Subscribes to test_topic and logs received messages
class TestAgnocastOnlySubscriberNode : public agnocast::Node
{
public:
  explicit TestAgnocastOnlySubscriberNode(
    const rclcpp::NodeOptions & options = rclcpp::NodeOptions())
  : agnocast::Node("test_agnocast_only_subscriber", options), received_count_(0)
  {
    rclcpp::CallbackGroup::SharedPtr callback_group_1 =
      this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions sub_options;
    sub_options.callback_group = callback_group_1;

    subscription_ = this->create_subscription<std_msgs::msg::String>(
      "test_topic", 10,
      [this](agnocast::ipc_shared_ptr<std_msgs::msg::String> msg) {
        received_count_++;
        RCLCPP_INFO(
          this->get_logger(), "Received: '%s' (count: %d)", msg->data.c_str(), received_count_);
      },
      sub_options);
  }

private:
  agnocast::Subscription<std_msgs::msg::String>::SharedPtr subscription_;
  int received_count_;
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  auto node = std::make_shared<TestAgnocastOnlySubscriberNode>();
  auto executor = std::make_shared<agnocast::AgnocastOnlyCallbackIsolatedExecutor>();
  executor->add_node(node);

  executor->spin();

  rclcpp::shutdown();
  return 0;
}

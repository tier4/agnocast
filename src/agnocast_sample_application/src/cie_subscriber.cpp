#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using std::placeholders::_1;

class CieSubscriber : public rclcpp::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr
    sub_dynamic2_;

  rclcpp::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_ros_;
  rclcpp::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_ros2_;

public:
  explicit CieSubscriber(const rclcpp::NodeOptions & options) : Node("minimal_subscriber", options)
  {
    rclcpp::CallbackGroup::SharedPtr group1 =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    rclcpp::CallbackGroup::SharedPtr group2 =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group1;
    sub_dynamic_ = agnocast::create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_topic", 1,
      [](const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> &
           message) {
        RCLCPP_INFO(
          rclcpp::get_logger("agnocast_sample_application"), "subscribe message in group1: id=%ld",
          message->id);
      },
      agnocast_options);

    rclcpp::SubscriptionOptions ros_options;
    ros_options.callback_group = group1;
    sub_ros_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/ros_topic", 1,
      [](const agnocast_sample_interfaces::msg::DynamicSizeArray::SharedPtr message) {
        RCLCPP_INFO(
          rclcpp::get_logger("agnocast_sample_application"),
          "subscribe ros message in group1: id=%ld", message->id);
      },
      ros_options);

    rclcpp::SubscriptionOptions ros_options2;
    ros_options2.callback_group = group2;
    sub_ros2_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/ros_other_topic", 1,
      [](const agnocast_sample_interfaces::msg::DynamicSizeArray::SharedPtr message) {
        RCLCPP_INFO(
          rclcpp::get_logger("agnocast_sample_application"),
          "subscribe ros other message in group2: id=%ld", message->id);
      },
      ros_options2);
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::CallbackIsolatedAgnocastExecutor executor;
  auto node = std::make_shared<CieSubscriber>(rclcpp::NodeOptions());
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

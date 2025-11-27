#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"

#include <iostream>

using std::placeholders::_1;

class NoRclcppSubscriber : public agnocast::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;

  void callback(
    const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(
      get_logger(), "I heard dynamic size array message with size: %zu", message->data.size());
  }

public:
  explicit NoRclcppSubscriber()
  {
    RCLCPP_INFO(get_logger(), "NoRclcppSubscriber node (name=%s) started.", get_name().c_str());

    auto group =
      std::make_shared<rclcpp::CallbackGroup>(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    sub_dynamic_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/my_topic", 1, std::bind(&NoRclcppSubscriber::callback, this, _1), agnocast_options);
  }
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);
  auto node = std::make_shared<NoRclcppSubscriber>();
  (void)node;
  return 0;
}

#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using agnocast_sample_interfaces::msg::DynamicSizeArray;
using std::placeholders::_1;

class MinimalSubscriber : public rclcpp::Node
{
private:
  rclcpp::Subscription<DynamicSizeArray>::SharedPtr subscription_;

  void topic_callback(const DynamicSizeArray::ConstSharedPtr msg)
  {
    RCLCPP_INFO(this->get_logger(), "Received message ID: %ld", msg->id);
  }

public:
  MinimalSubscriber() : Node("minimal_subscriber")
  {
    subscription_ = this->create_subscription<DynamicSizeArray>(
      "/my_topic",
      1,  // Queue depth (QoS)
      std::bind(&MinimalSubscriber::topic_callback, this, _1));
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<MinimalSubscriber>());
  rclcpp::shutdown();
  return 0;
}
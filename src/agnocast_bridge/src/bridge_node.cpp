#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sample_interfaces/msg/dynamic_size_array.hpp"

using std::placeholders::_1;

class BridgeNode : public rclcpp::Node
{
  std::shared_ptr<agnocast::CallbackSubscription<sample_interfaces::msg::DynamicSizeArray>>
    agnocast_subscriber_;
  rclcpp::Publisher<sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_;

  void agnocast_topic_callback(
    const agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(this->get_logger(), "bridge message agnocast->ros2 address: %p", message.get());
    const sample_interfaces::msg::DynamicSizeArray * raw = message.get();
    publisher_->publish(*raw);
  }

public:
  BridgeNode() : Node("bridge_node")
  {
    auto publisher_options = rclcpp::PublisherOptions();
    publisher_options.use_intra_process_comm = rclcpp::IntraProcessSetting::Enable;
    publisher_ = this->create_publisher<sample_interfaces::msg::DynamicSizeArray>(
      "/mytopic", 10, publisher_options);

    agnocast_subscriber_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      "/mytopic", 10, std::bind(&BridgeNode::agnocast_topic_callback, this, _1));
  }
};

int main(int argc, char * argv[])
{
  agnocast::initialize_agnocast();
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<BridgeNode>());
  rclcpp::shutdown();
  return 0;
}

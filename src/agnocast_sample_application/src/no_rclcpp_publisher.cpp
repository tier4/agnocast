#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"

#include <iostream>

class NoRclcppPublisher : public agnocast::Node
{
  agnocast::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr pub_;

  void timer_callback()
  {
    auto message = pub_->borrow_loaned_message();
    message->data.resize(100);
    pub_->publish(std::move(message));
    RCLCPP_INFO(get_logger(), "Published message with size: 100");
  }

public:
  explicit NoRclcppPublisher() : Node("no_rclcpp_publisher")
  {
    RCLCPP_INFO(get_logger(), "NoRclcppPublisher node (name=%s) started.", get_name().c_str());

    pub_ =
      this->create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>("/my_topic", 1);

    this->create_wall_timer(
      std::chrono::milliseconds(1000), std::bind(&NoRclcppPublisher::timer_callback, this));
  }
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);
  agnocast::AgnocastOnlySingleThreadedExecutor executor;
  auto node = std::make_shared<NoRclcppPublisher>();
  executor.add_node(node);
  executor.spin();
  return 0;
}

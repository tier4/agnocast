#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"

#include <chrono>

using namespace std::chrono_literals;

class NoRclcppTakeListener : public agnocast::Node
{
  agnocast::PollingSubscriber<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_;
  agnocast::TimerBase::SharedPtr timer_;

  void timer_callback()
  {
    auto message = sub_->take_data();
    if (message) {
      RCLCPP_INFO(
        get_logger(), "I heard dynamic size array message with id: %ld, size: %zu", message->id,
        message->data.size());
    }
  }

public:
  explicit NoRclcppTakeListener() : agnocast::Node("no_rclcpp_take_listener")
  {
    sub_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/my_topic", rclcpp::QoS(rclcpp::KeepLast(1)));

    timer_ = this->create_wall_timer(100ms, std::bind(&NoRclcppTakeListener::timer_callback, this));

    RCLCPP_INFO(get_logger(), "NoRclcppTakeListener started");
  }
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);
  agnocast::AgnocastOnlySingleThreadedExecutor executor;
  auto node = std::make_shared<NoRclcppTakeListener>();
  executor.add_node(node);
  executor.spin();
  return 0;
}

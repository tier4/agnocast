#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/executors/single_threaded_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <chrono>
#include <memory>

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

class MinimalRos2Publisher : public rclcpp::Node
{
private:
  int64_t count_;
  rclcpp::TimerBase::SharedPtr timer_;
  rclcpp::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_;

  void timer_callback()
  {
    auto loaned_message = publisher_->borrow_loaned_message();
    auto & message = loaned_message.get();

    message.id = count_;
    message.data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      message.data.push_back(i + count_);
    }

    publisher_->publish(std::move(loaned_message));
    RCLCPP_INFO(this->get_logger(), "publish message: id=%ld", count_++);
  }

public:
  MinimalRos2Publisher() : Node("minimal_ros2_publisher")
  {
    count_ = 0;

    rclcpp::QoS qos(1);
    qos.reliable();
    publisher_ =
      this->create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>("/my_topic", qos);

    timer_ = this->create_wall_timer(100ms, std::bind(&MinimalRos2Publisher::timer_callback, this));
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);
  rclcpp::executors::SingleThreadedExecutor executor;

  auto node = std::make_shared<MinimalRos2Publisher>();
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}
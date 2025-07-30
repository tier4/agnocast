#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

class CiePublisher : public rclcpp::Node
{
  int64_t count_;
  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr
    publisher_dynamic_;

  rclcpp::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_ros_;

  rclcpp::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_ros2_;

  void timer_callback()
  {
    agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> message =
      publisher_dynamic_->borrow_loaned_message();

    message->id = count_;
    message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      message->data.push_back(i + count_);
    }

    publisher_dynamic_->publish(std::move(message));
    RCLCPP_INFO(this->get_logger(), "publish message: id=%ld", count_);

    agnocast_sample_interfaces::msg::DynamicSizeArray ros_message;
    ros_message.id = count_;
    ros_message.data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      ros_message.data.push_back(i + count_);
    }

    publisher_ros_->publish(ros_message);
    publisher_ros2_->publish(ros_message);

    count_++;
  }

public:
  CiePublisher() : Node("minimal_publisher")
  {
    count_ = 0;

    publisher_dynamic_ =
      agnocast::create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
        this, "/my_topic", 1);

    publisher_ros_ =
      this->create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>("/ros_topic", 1);

    publisher_ros2_ = this->create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/ros_other_topic", 1);

    timer_ = this->create_wall_timer(100ms, std::bind(&CiePublisher::timer_callback, this));
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  auto node = std::make_shared<CiePublisher>();
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

class CiePublisher : public rclcpp::Node
{
  int64_t count_;

  rclcpp::TimerBase::SharedPtr timer_agnocast_;
  rclcpp::TimerBase::SharedPtr timer_ros_;
  rclcpp::TimerBase::SharedPtr timer_ros2_;

  agnocast::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr
    publisher_agnocast_;
  rclcpp::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_ros_;
  rclcpp::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_ros2_;

  rclcpp::CallbackGroup::SharedPtr cb_group_;

  void timer_callback_agnocast()
  {
    agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> message =
      publisher_agnocast_->borrow_loaned_message();

    message->id = count_;
    message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      message->data.push_back(i + count_);
    }

    publisher_agnocast_->publish(std::move(message));
    RCLCPP_INFO(this->get_logger(), "publish message: id=%ld to /my_topic", count_);
    count_++;
  }

  void timer_callback_ros()
  {
    agnocast_sample_interfaces::msg::DynamicSizeArray ros_message;
    ros_message.id = count_;
    ros_message.data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      ros_message.data.push_back(i + count_);
    }

    publisher_ros_->publish(ros_message);
    RCLCPP_INFO(this->get_logger(), "publish message: id=%ld to /ros_topic", count_);
    count_++;
  }

  void timer_callback_ros2()
  {
    agnocast_sample_interfaces::msg::DynamicSizeArray ros_message;
    ros_message.id = count_;
    ros_message.data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      ros_message.data.push_back(i + count_);
    }

    publisher_ros2_->publish(ros_message);
    RCLCPP_INFO(this->get_logger(), "publish message: id=%ld to /ros_other_topic", count_);
    count_++;
  }

public:
  CiePublisher() : Node("cie_publisher"), count_(1)
  {
    publisher_agnocast_ =
      agnocast::create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
        this, "/my_topic", 1);
    publisher_ros_ =
      this->create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>("/ros_topic", 1);
    publisher_ros2_ = this->create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/ros_other_topic", 1);

    cb_group_ = this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    // All timers belong to the same callback group, so the count_ is incremented properly even
    // though no mutex is used.
    timer_agnocast_ = this->create_wall_timer(
      300ms, std::bind(&CiePublisher::timer_callback_agnocast, this), cb_group_);
    timer_ros_ =
      this->create_wall_timer(300ms, std::bind(&CiePublisher::timer_callback_ros, this), cb_group_);
    timer_ros2_ = this->create_wall_timer(
      300ms, std::bind(&CiePublisher::timer_callback_ros2, this), cb_group_);
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::CallbackIsolatedAgnocastExecutor executor;
  auto node = std::make_shared<CiePublisher>();
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

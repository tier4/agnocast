#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "sample_interfaces/msg/static_size_array.hpp"

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

class MinimalPublisher : public rclcpp::Node
{
  void assign_data(sample_interfaces::msg::StaticSizeArray & data)
  {
    for (int i = 0; i < 1000; i++) {
      data.data[i] = i;
    }
  }

  void timer_callback()
  {
    {
      agnocast::ipc_shared_ptr<sample_interfaces::msg::DynamicSizeArray> message =
        publisher_dynamic1_->borrow_loaned_message();
      message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
      for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
        message->data.push_back(i);
      }

      // In order to test move constructor
      auto moved_message = std::move(message);
      publisher_dynamic1_->publish(std::move(moved_message));
      RCLCPP_INFO(this->get_logger(), "publish dynamic message 1");
    }

    {
      agnocast::ipc_shared_ptr<sample_interfaces::msg::DynamicSizeArray> message =
        publisher_dynamic2_->borrow_loaned_message();
      message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
      for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
        message->data.push_back(i);
      }
      publisher_dynamic2_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish dynamic message 2");
    }

    {
      agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> message =
        publisher_static1_->borrow_loaned_message();
      assign_data(*message);
      publisher_static1_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish static message 1");
    }

    {
      agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> message =
        publisher_static2_->borrow_loaned_message();
      assign_data(*message);
      publisher_static2_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish static message 2");
    }
  }

  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_dynamic1_;
  agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_dynamic2_;
  agnocast::Publisher<sample_interfaces::msg::StaticSizeArray>::SharedPtr publisher_static1_;
  agnocast::Publisher<sample_interfaces::msg::StaticSizeArray>::SharedPtr publisher_static2_;

  agnocast::Publisher<sample_interfaces::msg::StaticSizeArray>::SharedPtr
    publisher_transient_local_;
  agnocast::Publisher<sample_interfaces::msg::StaticSizeArray>::SharedPtr
    publisher_transient_local_with_flag_;

public:
  MinimalPublisher() : Node("minimal_publisher")
  {
    timer_ = this->create_wall_timer(100ms, std::bind(&MinimalPublisher::timer_callback, this));
    publisher_dynamic1_ = agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_dynamic_topic", 10);
    publisher_dynamic2_ = agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_dynamic_topic", 10);
    publisher_static1_ = agnocast::create_publisher<sample_interfaces::msg::StaticSizeArray>(
      this, "/my_static_topic", 10);
    publisher_static2_ = agnocast::create_publisher<sample_interfaces::msg::StaticSizeArray>(
      this, "/my_static_topic", 10);

    {
      publisher_transient_local_ =
        agnocast::create_publisher<sample_interfaces::msg::StaticSizeArray>(
          this, "/my_transient_local_topic", rclcpp::QoS(1).transient_local());
      agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> message =
        publisher_transient_local_->borrow_loaned_message();
      assign_data(*message);
      publisher_transient_local_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish transient_local message");
    }

    {
      publisher_transient_local_with_flag_ =
        agnocast::create_publisher<sample_interfaces::msg::StaticSizeArray>(
          this, "/my_transient_local_topic_with_flag", rclcpp::QoS(1).transient_local(), false);
      agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> message =
        publisher_transient_local_with_flag_->borrow_loaned_message();
      assign_data(*message);
      publisher_transient_local_with_flag_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish transient_local message with flag");
    }
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  executor.add_node(std::make_shared<MinimalPublisher>());
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

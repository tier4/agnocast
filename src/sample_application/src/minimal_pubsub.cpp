#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "sample_interfaces/msg/static_size_array.hpp"

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

using std::placeholders::_1;

class MinimalPubSub : public rclcpp::Node
{
  void static_topic_callback(
    const agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> & message)
  {
    RCLCPP_INFO(
      this->get_logger(), "I heard static message: addr=%016lx",
      reinterpret_cast<uint64_t>(message.get()));
  }

  void dynamic_topic_callback(
    const agnocast::ipc_shared_ptr<sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(
      this->get_logger(), "I heard dynamic message: addr=%016lx",
      reinterpret_cast<uint64_t>(message.get()));
  }

  void timer_callback()
  {
    {
      agnocast::ipc_shared_ptr<sample_interfaces::msg::DynamicSizeArray> message =
        pub_dynamic_->borrow_loaned_message();
      message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
      for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
        message->data.push_back(i);
      }
      pub_dynamic_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish dynamic message");
    }

    {
      agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> message =
        pub_static_->borrow_loaned_message();
      for (int i = 0; i < 1000; i++) {
        message->data[i] = i;
      }
      pub_static_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "publish static message");
    }
  }

  agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>::SharedPtr pub_dynamic_;
  agnocast::Publisher<sample_interfaces::msg::StaticSizeArray>::SharedPtr pub_static_;
  agnocast::Subscription<sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr sub_static_;
  rclcpp::TimerBase::SharedPtr timer_;

public:
  MinimalPubSub() : Node("minimal_pubsub")
  {
    pub_dynamic_ = agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_dynamic_topic", 10);
    pub_static_ = agnocast::create_publisher<sample_interfaces::msg::StaticSizeArray>(
      this, "/my_static_topic", 10);
    sub_dynamic_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_dynamic_topic", 10, std::bind(&MinimalPubSub::dynamic_topic_callback, this, _1));
    sub_static_ = agnocast::create_subscription<sample_interfaces::msg::StaticSizeArray>(
      this, "/my_static_topic", 10, std::bind(&MinimalPubSub::static_topic_callback, this, _1));
    timer_ = this->create_wall_timer(100ms, std::bind(&MinimalPubSub::timer_callback, this));
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  executor.add_node(std::make_shared<MinimalPubSub>());
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

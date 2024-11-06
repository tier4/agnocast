#include "agnocast.hpp"

#include <rclcpp/rclcpp.hpp>

#include <std_msgs/msg/string.hpp>

#include <chrono>
#include <memory>

using namespace std::chrono_literals;

class CallbackGroupTestTalker : public rclcpp::Node
{
public:
  CallbackGroupTestTalker() : Node("callback_group_test_talker")
  {
    pub1_ = agnocast::create_publisher<std_msgs::msg::String>("/topic1", 10);
    pub2_ = agnocast::create_publisher<std_msgs::msg::String>("/topic2", 10);

    timer_ = this->create_wall_timer(
      5000ms, std::bind(&CallbackGroupTestTalker::publish_test_messages, this));

    RCLCPP_INFO(this->get_logger(), "Talker initialized");
  }

private:
  void publish_test_messages()
  {
    auto msg1 = pub1_->borrow_loaned_message();
    msg1->data = "Test message 1";
    pub1_->publish(std::move(msg1));

    auto msg2 = pub2_->borrow_loaned_message();
    msg2->data = "Test message 2";
    pub2_->publish(std::move(msg2));
  }

  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::Publisher<std_msgs::msg::String>::SharedPtr pub1_;
  agnocast::Publisher<std_msgs::msg::String>::SharedPtr pub2_;
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  auto node = std::make_shared<CallbackGroupTestTalker>();
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

#include "std_msgs/msg/int64.hpp"

#include <chrono>
using namespace std::chrono_literals;

class TestTakeSubscriber : public rclcpp::Node
{
  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::TakeSubscription<std_msgs::msg::Int64>::SharedPtr sub_;
  uint64_t count_;
  uint64_t sub_num_;

  void timer_callback()
  {
    auto message = sub_->take();
    if (message) {
      RCLCPP_INFO(this->get_logger(), "%ld", message->data);
      count_++;
    }

    if (count_ == sub_num_) {
      RCLCPP_INFO(this->get_logger(), "All messages received. Shutting down.");
      timer_->cancel();
      rclcpp::shutdown();
    }
  }

public:
  TestTakeSubscriber() : Node("test_take_subscription")
  {
    this->declare_parameter<int64_t>("qos_depth", 10);
    this->declare_parameter<bool>("transient_local", true);
    this->declare_parameter<int64_t>("sub_num", 10);

    int64_t qos_depth = this->get_parameter("qos_depth").as_int();
    rclcpp::QoS qos = rclcpp::QoS(rclcpp::KeepLast(qos_depth));
    if (this->get_parameter("transient_local").as_bool()) {
      qos.transient_local();
    }

    count_ = 0;
    sub_num_ = this->get_parameter("sub_num").as_int();
    sub_ =
      std::make_shared<agnocast::TakeSubscription<std_msgs::msg::Int64>>(this, "/test_topic", qos);
    timer_ = this->create_wall_timer(10ms, std::bind(&TestTakeSubscriber::timer_callback, this));
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  executor.add_node(std::make_shared<TestTakeSubscriber>());
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

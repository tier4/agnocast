#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

#include "std_msgs/msg/int64.hpp"

using std::placeholders::_1;

class TestSubscriber : public rclcpp::Node
{
  agnocast::Subscription<std_msgs::msg::Int64>::SharedPtr sub_;
  uint64_t count_;
  uint64_t sub_num_;

  void callback(const agnocast::ipc_shared_ptr<std_msgs::msg::Int64> & message)
  {
    RCLCPP_INFO(this->get_logger(), "%ld", message->data);

    count_++;
    if (count_ == sub_num_) {
      RCLCPP_INFO(this->get_logger(), "All messages received. Shutting down.");
      rclcpp::shutdown();
    }
  }

public:
  TestSubscriber() : Node("test_subscription")
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
    sub_ = agnocast::create_subscription<std_msgs::msg::Int64>(
      this, "/test_topic", qos, std::bind(&TestSubscriber::callback, this, _1));
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  executor.add_node(std::make_shared<TestSubscriber>());
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

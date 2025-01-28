#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

#include "std_msgs/msg/int64.hpp"

#include <chrono>

using namespace std::chrono_literals;

class TestPublisher : public rclcpp::Node
{
  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::Publisher<std_msgs::msg::Int64>::SharedPtr publisher_;
  int64_t count_;
  int64_t pub_num_;

  void timer_callback()
  {
    if (publisher_->get_subscription_count() < 2) {
      return;
    }

    agnocast::ipc_shared_ptr<std_msgs::msg::Int64> message = publisher_->borrow_loaned_message();
    message->data = count_;
    publisher_->publish(std::move(message));
    RCLCPP_INFO(this->get_logger(), "%ld", count_);
    count_++;

    if (count_ == pub_num_) {
      RCLCPP_INFO(this->get_logger(), "All messages published. Shutting down.");
      timer_->cancel();
      rclcpp::shutdown();
    }
  }

public:
  TestPublisher() : Node("test_publisher")
  {
    this->declare_parameter<int64_t>("qos_depth", 10);
    this->declare_parameter<bool>("transient_local", true);
    this->declare_parameter<int64_t>("init_pub_num", 10);
    this->declare_parameter<int64_t>("pub_num", 10);
    int64_t qos_depth = this->get_parameter("qos_depth").as_int();
    bool transient_local = this->get_parameter("transient_local").as_bool();
    int64_t init_pub_num = this->get_parameter("init_pub_num").as_int();
    int64_t pub_num = this->get_parameter("pub_num").as_int();

    rclcpp::QoS qos = rclcpp::QoS(rclcpp::KeepLast(qos_depth));
    if (transient_local) {
      qos.transient_local();
    }
    publisher_ = agnocast::create_publisher<std_msgs::msg::Int64>(this, "/test_topic", qos);
    count_ = 0;
    pub_num_ = init_pub_num + pub_num;

    // Initial publish
    for (int i = 0; i < init_pub_num; i++) {
      agnocast::ipc_shared_ptr<std_msgs::msg::Int64> message = publisher_->borrow_loaned_message();
      message->data = count_;
      publisher_->publish(std::move(message));
      RCLCPP_INFO(this->get_logger(), "%ld", count_);
      count_++;
    }

    timer_ = this->create_wall_timer(10ms, std::bind(&TestPublisher::timer_callback, this));
    sleep(3);  // wait for the subscription to be established
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  executor.add_node(std::make_shared<TestPublisher>());
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

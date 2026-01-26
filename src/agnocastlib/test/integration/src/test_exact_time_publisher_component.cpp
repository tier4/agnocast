#include "agnocast/agnocast.hpp"

#include <rclcpp/rclcpp.hpp>
#include <rclcpp_components/register_node_macro.hpp>

#include <sensor_msgs/msg/imu.hpp>

#include <chrono>

using namespace std::chrono_literals;

namespace agnocastlib_test
{

class TestExactTimePublisherComponent : public rclcpp::Node
{
public:
  explicit TestExactTimePublisherComponent(const rclcpp::NodeOptions & options)
  : Node("test_exact_time_publisher", options), count_(0)
  {
    pub1_ = agnocast::create_publisher<sensor_msgs::msg::Imu>(this, "imu_topic1", rclcpp::QoS(10));
    pub2_ = agnocast::create_publisher<sensor_msgs::msg::Imu>(this, "imu_topic2", rclcpp::QoS(10));
    timer_ = this->create_wall_timer(100ms, [this]() { publish(); });
  }

private:
  void publish()
  {
    auto now = this->now();

    auto msg1 = pub1_->borrow_loaned_message();
    msg1->header.stamp = now;
    pub1_->publish(std::move(msg1));

    auto msg2 = pub2_->borrow_loaned_message();
    msg2->header.stamp = now;
    pub2_->publish(std::move(msg2));

    if (++count_ >= 5) {
      timer_->cancel();
    }
  }

  agnocast::Publisher<sensor_msgs::msg::Imu>::SharedPtr pub1_;
  agnocast::Publisher<sensor_msgs::msg::Imu>::SharedPtr pub2_;
  rclcpp::TimerBase::SharedPtr timer_;
  int count_;
};

}  // namespace agnocastlib_test

RCLCPP_COMPONENTS_REGISTER_NODE(agnocastlib_test::TestExactTimePublisherComponent)

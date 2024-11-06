#include "agnocast.hpp"

#include <rclcpp/rclcpp.hpp>

#include <std_msgs/msg/string.hpp>

#include <chrono>
#include <memory>
#include <thread>

using namespace std::chrono_literals;

class CallbackGroupTestListener : public rclcpp::Node
{
public:
  CallbackGroupTestListener() : Node("callback_group_test_listener")
  {
    mutex_callback_group_ =
      this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions sub_options;
    sub_options.callback_group = mutex_callback_group_;

    sub1_ = agnocast::create_subscription<std_msgs::msg::String>(
      get_node_base_interface(), "/topic1", rclcpp::QoS(10),
      std::bind(&CallbackGroupTestListener::sub_callback1, this, std::placeholders::_1),
      sub_options);

    sub2_ = agnocast::create_subscription<std_msgs::msg::String>(
      get_node_base_interface(), "/topic2", 10,
      std::bind(&CallbackGroupTestListener::sub_callback2, this, std::placeholders::_1),
      sub_options);

    timer_ = this->create_wall_timer(
      5s, std::bind(&CallbackGroupTestListener::timer_callback, this), mutex_callback_group_);

    RCLCPP_INFO(
      this->get_logger(),
      "Listener initialized. Timer and subscription callbacks are in the same mutually exclusive "
      "callback group.");
  }

private:
  std::string get_thread_id()
  {
    std::stringstream ss;
    ss << std::this_thread::get_id();
    return ss.str();
  }

  void timer_callback()
  {
    auto start_time = std::chrono::steady_clock::now();
    auto thread_id = get_thread_id();
    RCLCPP_INFO(
      this->get_logger(), "Starting timer callback - Thread ID: %ld, Time: %ld",
      syscall(SYS_gettid), std::chrono::system_clock::now().time_since_epoch().count());

    std::this_thread::sleep_for(1s);

    auto end_time = std::chrono::steady_clock::now();
    auto duration =
      std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();

    RCLCPP_INFO(
      this->get_logger(), "Finished timer callback - Thread ID: %ld, Duration: %ld ms",
      syscall(SYS_gettid), duration);
  }

  void sub_callback1(const agnocast::ipc_shared_ptr<std_msgs::msg::String> & msg)
  {
    auto start_time = std::chrono::steady_clock::now();
    auto thread_id = get_thread_id();
    RCLCPP_INFO(
      this->get_logger(),
      "Starting subscription callback1 - Thread ID: %ld, Time: %ld, Message: %s",
      syscall(SYS_gettid), std::chrono::system_clock::now().time_since_epoch().count(),
      msg->data.c_str());

    std::this_thread::sleep_for(1s);

    auto end_time = std::chrono::steady_clock::now();
    auto duration =
      std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();

    RCLCPP_INFO(
      this->get_logger(), "Finished subscription callback1 - Thread ID: %ld, Duration: %ld ms",
      syscall(SYS_gettid), duration);
  }

  void sub_callback2(const agnocast::ipc_shared_ptr<std_msgs::msg::String> & msg)
  {
    auto start_time = std::chrono::steady_clock::now();
    auto thread_id = get_thread_id();
    RCLCPP_INFO(
      this->get_logger(),
      "Starting subscription callback2 - Thread ID: %ld, Time: %ld, Message: %s",
      syscall(SYS_gettid), std::chrono::system_clock::now().time_since_epoch().count(),
      msg->data.c_str());

    std::this_thread::sleep_for(1s);

    auto end_time = std::chrono::steady_clock::now();
    auto duration =
      std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();

    RCLCPP_INFO(
      this->get_logger(), "Finished subscription callback2 - Thread ID: %ld, Duration: %ld ms",
      syscall(SYS_gettid), duration);
  }

  rclcpp::CallbackGroup::SharedPtr mutex_callback_group_;
  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::Subscription<std_msgs::msg::String>::SharedPtr sub1_;
  agnocast::Subscription<std_msgs::msg::String>::SharedPtr sub2_;
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  auto node = std::make_shared<CallbackGroupTestListener>();
  agnocast::MultiThreadedAgnocastExecutor executor;
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

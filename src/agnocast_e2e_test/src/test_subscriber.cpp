#include "agnocast/agnocast.hpp"
#include "rclcpp/rclcpp.hpp"

#include "std_msgs/msg/int64.hpp"

using std::placeholders::_1;

class TestSubscriber : public rclcpp::Node
{
  agnocast::Subscription<std_msgs::msg::Int64>::SharedPtr sub_;
  uint64_t count_;
  uint64_t target_sub_num_;
  bool forever_;

  void callback(const agnocast::ipc_shared_ptr<std_msgs::msg::Int64> & message)
  {
    RCLCPP_INFO(this->get_logger(), "Receiving %ld.", message->data);

    count_++;
    if (count_ == target_sub_num_) {
      RCLCPP_INFO(this->get_logger(), "All messages received. Shutting down.");
      std::cout << std::flush;
      sleep(3);  // HACK: wait for other nodes in the same container

      if (!forever_) {
        rclcpp::shutdown();
      }
    }
  }

public:
  explicit TestSubscriber(const rclcpp::NodeOptions & options) : Node("test_subscription", options)
  {
    this->declare_parameter<int64_t>("qos_depth", 10);
    this->declare_parameter<bool>("transient_local", true);
    this->declare_parameter<int64_t>("sub_num", 10);
    this->declare_parameter<bool>("forever", false);
    forever_ = this->get_parameter("forever").as_bool();

    int64_t qos_depth = this->get_parameter("qos_depth").as_int();
    rclcpp::QoS qos = rclcpp::QoS(rclcpp::KeepLast(qos_depth));
    if (this->get_parameter("transient_local").as_bool()) {
      qos.transient_local();
    }

    count_ = 0;
    target_sub_num_ = this->get_parameter("sub_num").as_int();

    auto cbg = this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions sub_options;
    sub_options.callback_group = cbg;
    sub_ = agnocast::create_subscription<std_msgs::msg::Int64>(
      this, "/test_topic", qos, std::bind(&TestSubscriber::callback, this, _1), sub_options);
  }
};

#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(TestSubscriber)

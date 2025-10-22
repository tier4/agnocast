#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using std::placeholders::_1;
using namespace std::chrono_literals;

class MinimalSubscriber : public rclcpp::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr pub_dynamic_;
  rclcpp::TimerBase::SharedPtr timer_;
  int64_t count_;

  void subscription_callback(
    const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(this->get_logger(), "subscribe message: id=%ld", message->id);
  }

  void timer_callback()
  {
    agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> pub_message =
      pub_dynamic_->borrow_loaned_message();
    pub_message->id = count_;
    pub_message->data.clear();
    pub_message->data.push_back(count_);

    pub_dynamic_->publish(std::move(pub_message));
    RCLCPP_INFO(this->get_logger(), "published message: id=%ld to /my_topic_2", count_);
    count_++;
  }

public:
  explicit MinimalSubscriber(const rclcpp::NodeOptions & options)
  : Node("cie_subscriber", options), count_(0)
  {
    rclcpp::CallbackGroup::SharedPtr group =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    sub_dynamic_ = agnocast::create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_topic", 1, std::bind(&MinimalSubscriber::subscription_callback, this, _1),
      agnocast_options);

    pub_dynamic_ = agnocast::create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_topic_2", 1);

    timer_ = this->create_wall_timer(200ms, std::bind(&MinimalSubscriber::timer_callback, this));
  }
};

#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(MinimalSubscriber)

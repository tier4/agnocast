#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using namespace std::chrono_literals;

class TakeSubscriberMyTopic2 : public rclcpp::Node
{
  agnocast::TakeSubscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr take_sub_;
  agnocast::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr pub_dynamic_;
  rclcpp::TimerBase::SharedPtr timer_;

  void timer_callback()
  {
    auto message = take_sub_->take();
    if (message) {
      RCLCPP_INFO(this->get_logger(), "took message from /my_topic_2: id=%ld", message->id);

      agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> pub_message =
        pub_dynamic_->borrow_loaned_message();
      pub_message->id = message->id;
      pub_message->data = message->data;

      pub_dynamic_->publish(std::move(pub_message));
      RCLCPP_INFO(this->get_logger(), "published message: id=%ld to /my_topic_3", message->id);
    }
  }

public:
  explicit TakeSubscriberMyTopic2(const rclcpp::NodeOptions & options) : Node("take_subscriber_my_topic_2", options)
  {
    take_sub_ = std::make_shared<agnocast::TakeSubscription<agnocast_sample_interfaces::msg::DynamicSizeArray>>(
      this, "/my_topic_2", rclcpp::QoS(1));

    pub_dynamic_ = agnocast::create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_topic_3", 1);

    timer_ = this->create_wall_timer(100ms, std::bind(&TakeSubscriberMyTopic2::timer_callback, this));
  }
};

#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(TakeSubscriberMyTopic2)
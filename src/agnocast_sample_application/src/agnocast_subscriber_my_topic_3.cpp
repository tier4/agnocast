#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using std::placeholders::_1;

class AgnocastSubscriberMyTopic3 : public rclcpp::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr subscription_;

  void topic_callback(const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & msg)
  {
    RCLCPP_INFO(this->get_logger(), "Agnocast received message from /my_topic_3: id=%ld", msg->id);
  }

public:
  explicit AgnocastSubscriberMyTopic3(const rclcpp::NodeOptions & options) : Node("agnocast_subscriber_my_topic_3", options)
  {
    rclcpp::CallbackGroup::SharedPtr group =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    subscription_ = agnocast::create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      this, "/my_topic_3", 1, std::bind(&AgnocastSubscriberMyTopic3::topic_callback, this, _1), agnocast_options);
  }
};

#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(AgnocastSubscriberMyTopic3)
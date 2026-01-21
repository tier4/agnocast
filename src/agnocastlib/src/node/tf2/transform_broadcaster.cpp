#include "agnocast/node/tf2/transform_broadcaster.hpp"

namespace agnocast
{

TransformBroadcaster::TransformBroadcaster(agnocast::Node & node, const rclcpp::QoS & qos)
: publisher_(node.create_publisher<tf2_msgs::msg::TFMessage>("/tf", qos))
{
}

void TransformBroadcaster::sendTransform(const geometry_msgs::msg::TransformStamped & transform)
{
  sendTransform(std::vector<geometry_msgs::msg::TransformStamped>{transform});
}

void TransformBroadcaster::sendTransform(
  const std::vector<geometry_msgs::msg::TransformStamped> & transforms)
{
  auto msg = publisher_->borrow_loaned_message();
  msg->transforms = transforms;
  publisher_->publish(std::move(msg));
}

}  // namespace agnocast

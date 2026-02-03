#include "agnocast/node/tf2/transform_broadcaster.hpp"

#include <vector>

namespace agnocast
{

TransformBroadcaster::TransformBroadcaster(agnocast::Node & node, const rclcpp::QoS & qos)
: publisher_(node.create_publisher<tf2_msgs::msg::TFMessage>("/tf", qos))
{
}

void TransformBroadcaster::sendTransform(const geometry_msgs::msg::TransformStamped & msgtf)
{
  std::vector<geometry_msgs::msg::TransformStamped> v1;
  v1.push_back(msgtf);
  sendTransform(v1);
}

void TransformBroadcaster::sendTransform(
  const std::vector<geometry_msgs::msg::TransformStamped> & msgtf)
{
  auto msg = publisher_->borrow_loaned_message();
  for (std::vector<geometry_msgs::msg::TransformStamped>::const_iterator it = msgtf.begin();
       it != msgtf.end(); ++it) {
    msg->transforms.push_back(*it);
  }
  publisher_->publish(std::move(msg));
}

}  // namespace agnocast

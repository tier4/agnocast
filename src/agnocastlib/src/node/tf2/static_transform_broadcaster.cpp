#include "agnocast/node/tf2/static_transform_broadcaster.hpp"

#include <vector>

namespace agnocast
{

StaticTransformBroadcaster::StaticTransformBroadcaster(
  agnocast::Node & node, const rclcpp::QoS & qos)
: publisher_(node.create_publisher<tf2_msgs::msg::TFMessage>("/tf_static", qos))
{
}

void StaticTransformBroadcaster::sendTransform(const geometry_msgs::msg::TransformStamped & msgtf)
{
  std::vector<geometry_msgs::msg::TransformStamped> v1;
  v1.push_back(msgtf);
  sendTransform(v1);
}

void StaticTransformBroadcaster::sendTransform(
  const std::vector<geometry_msgs::msg::TransformStamped> & msgtf)
{
  for (auto it_in = msgtf.begin(); it_in != msgtf.end(); ++it_in) {
    bool match_found = false;
    for (auto it_msg = net_message_.transforms.begin(); it_msg != net_message_.transforms.end();
         ++it_msg) {
      if (it_in->child_frame_id == it_msg->child_frame_id) {
        *it_msg = *it_in;
        match_found = true;
        break;
      }
    }
    if (!match_found) {
      net_message_.transforms.push_back(*it_in);
    }
  }

  auto msg = publisher_->borrow_loaned_message();
  msg->transforms = net_message_.transforms;
  publisher_->publish(std::move(msg));
}

}  // namespace agnocast

#include "agnocast/node/tf2/transform_listener.hpp"

#include "rclcpp/logging.hpp"

namespace agnocast
{

TransformListener::TransformListener(
  tf2::BufferCore & buffer, agnocast::Node & node, const rclcpp::QoS & qos,
  const rclcpp::QoS & static_qos)
: buffer_(buffer)
{
  // Subscribe to /tf (dynamic transforms)
  tf_subscription_ = node.create_subscription<tf2_msgs::msg::TFMessage>(
    "/tf", qos, [this](agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg) {
      subscription_callback(std::move(msg), false);
    });

  // Subscribe to /tf_static (static transforms)
  tf_static_subscription_ = node.create_subscription<tf2_msgs::msg::TFMessage>(
    "/tf_static", static_qos, [this](agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg) {
      subscription_callback(std::move(msg), true);
    });
}

void TransformListener::subscription_callback(
  agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg, bool is_static)
{
  for (const auto & transform : msg->transforms) {
    try {
      buffer_.setTransform(transform, kDefaultAuthority, is_static);
    } catch (const tf2::TransformException & ex) {
      RCLCPP_ERROR(rclcpp::get_logger("agnocast.tf2"), "Failed to set transform: %s", ex.what());
    }
  }
}

}  // namespace agnocast

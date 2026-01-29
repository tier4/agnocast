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
  const tf2_msgs::msg::TFMessage & msg_in = *msg;
  // TODO(tfoote) find a way to get the authority
  std::string authority = "Authority undetectable";
  for (size_t i = 0u; i < msg_in.transforms.size(); i++) {
    try {
      buffer_.setTransform(msg_in.transforms[i], authority, is_static);
    } catch (const tf2::TransformException & ex) {
      // /\todo Use error reporting
      std::string temp = ex.what();
      RCLCPP_ERROR(
        rclcpp::get_logger("tf2_listener"),
        "Failure to set received transform from %s to %s with error: %s\n",
        msg_in.transforms[i].child_frame_id.c_str(), msg_in.transforms[i].header.frame_id.c_str(),
        temp.c_str());
    }
  }
}

}  // namespace agnocast

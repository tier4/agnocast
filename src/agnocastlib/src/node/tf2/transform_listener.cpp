#include "agnocast/node/tf2/transform_listener.hpp"

#include "rclcpp/logging.hpp"

namespace agnocast
{

TransformListener::TransformListener(
  tf2::BufferCore & buffer, agnocast::Node & node, bool spin_thread, const rclcpp::QoS & qos,
  const rclcpp::QoS & static_qos)
: buffer_(buffer), spin_thread_(spin_thread)
{
  using callback_t = std::function<void(agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> &&)>;
  callback_t cb =
    std::bind(&TransformListener::subscription_callback, this, std::placeholders::_1, false);
  callback_t static_cb =
    std::bind(&TransformListener::subscription_callback, this, std::placeholders::_1, true);

  if (spin_thread_) {
    // Create new callback group for tf_subscription_ and tf_static_subscription_
    callback_group_ =
      node.create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive, false);

    agnocast::SubscriptionOptions tf_options;
    agnocast::SubscriptionOptions tf_static_options;
    tf_options.callback_group = callback_group_;
    tf_static_options.callback_group = callback_group_;

    tf_subscription_ =
      node.create_subscription<tf2_msgs::msg::TFMessage>("/tf", qos, std::move(cb), tf_options);
    tf_static_subscription_ = node.create_subscription<tf2_msgs::msg::TFMessage>(
      "/tf_static", static_qos, std::move(static_cb), tf_static_options);

    // Create executor with dedicated thread to spin.
    executor_ = std::make_shared<agnocast::AgnocastOnlySingleThreadedExecutor>();
    executor_->add_callback_group(callback_group_);
    dedicated_listener_thread_ = std::make_unique<std::thread>([&]() { executor_->spin(); });
    // Tell the buffer we have a dedicated thread to enable timeouts
    buffer_.setUsingDedicatedThread(true);
  } else {
    tf_subscription_ =
      node.create_subscription<tf2_msgs::msg::TFMessage>("/tf", qos, std::move(cb));
    tf_static_subscription_ = node.create_subscription<tf2_msgs::msg::TFMessage>(
      "/tf_static", static_qos, std::move(static_cb));
  }
}

TransformListener::~TransformListener()
{
  if (spin_thread_) {
    // TODO(Koichi98): Implement cancel() in AgnocastOnlyExecutor to stop the executor gracefully
    if (dedicated_listener_thread_ && dedicated_listener_thread_->joinable()) {
      dedicated_listener_thread_->join();
    }
  }
}

void TransformListener::subscription_callback(
  agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg, bool is_static)
{
  const tf2_msgs::msg::TFMessage & msg_in = *msg;
  std::string authority = "Authority undetectable";
  for (size_t i = 0u; i < msg_in.transforms.size(); i++) {
    try {
      buffer_.setTransform(msg_in.transforms[i], authority, is_static);
    } catch (const tf2::TransformException & ex) {
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

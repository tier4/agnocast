#ifndef AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_
#define AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_

#include "agnocast/agnocast.hpp"
#include "tf2/buffer_core.h"

#include "tf2_msgs/msg/tf_message.hpp"

#include <memory>
#include <string>

namespace agnocast
{

/// \brief Default QoS for dynamic transform listening (matches tf2_ros::DynamicListenerQoS)
inline rclcpp::QoS DynamicListenerQoS(size_t depth = 100)
{
  return rclcpp::QoS(depth);
}

/// \brief Default QoS for static transform listening (matches tf2_ros::StaticListenerQoS)
inline rclcpp::QoS StaticListenerQoS(size_t depth = 100)
{
  return rclcpp::QoS(depth).transient_local();
}

/// \brief Listens for transforms via Agnocast zero-copy IPC.
///
/// This class subscribes to /tf and /tf_static topics using Agnocast's
/// zero-copy shared memory transport, and populates a tf2::BufferCore
/// with the received transforms.
class TransformListener
{
public:
  /// \brief Constructor with tf2::BufferCore
  ///
  /// \param buffer The buffer to populate with received transforms
  /// \param node Reference to an agnocast::Node
  /// \param qos QoS for /tf subscription (default: depth=100)
  /// \param static_qos QoS for /tf_static subscription (default: depth=100, transient_local)
  TransformListener(
    tf2::BufferCore & buffer, agnocast::Node & node, const rclcpp::QoS & qos = DynamicListenerQoS(),
    const rclcpp::QoS & static_qos = StaticListenerQoS());

  virtual ~TransformListener() = default;

private:
  /// \brief Callback for /tf and /tf_static messages
  void subscription_callback(
    agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg, bool is_static);

  tf2::BufferCore & buffer_;
  agnocast::Subscription<tf2_msgs::msg::TFMessage>::SharedPtr tf_subscription_;
  agnocast::Subscription<tf2_msgs::msg::TFMessage>::SharedPtr tf_static_subscription_;

  static constexpr const char * kDefaultAuthority = "default_authority";
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_

#ifndef AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_
#define AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_

#include "agnocast/agnocast.hpp"
#include "agnocast/node/agnocast_only_single_threaded_executor.hpp"
#include "rclcpp/callback_group.hpp"
#include "tf2/buffer_core.h"

#include "tf2_msgs/msg/tf_message.hpp"

#include <memory>
#include <string>
#include <thread>

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
  /// \param spin_thread If true, creates a dedicated thread for TF callbacks.
  ///                    This allows using timeout-based lookupTransform without deadlock.
  /// \param qos QoS for /tf subscription (default: depth=100)
  /// \param static_qos QoS for /tf_static subscription (default: depth=100, transient_local)
  TransformListener(
    tf2::BufferCore & buffer, agnocast::Node & node, bool spin_thread = true,
    const rclcpp::QoS & qos = DynamicListenerQoS(),
    const rclcpp::QoS & static_qos = StaticListenerQoS());

  virtual ~TransformListener();

private:
  /// \brief Callback for /tf and /tf_static messages
  void subscription_callback(
    agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg, bool is_static);

  tf2::BufferCore & buffer_;
  bool spin_thread_{false};
  rclcpp::CallbackGroup::SharedPtr callback_group_{nullptr};
  std::unique_ptr<std::thread> dedicated_listener_thread_{nullptr};
  std::shared_ptr<agnocast::AgnocastOnlySingleThreadedExecutor> executor_{nullptr};
  agnocast::Subscription<tf2_msgs::msg::TFMessage>::SharedPtr tf_subscription_;
  agnocast::Subscription<tf2_msgs::msg::TFMessage>::SharedPtr tf_static_subscription_;
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_

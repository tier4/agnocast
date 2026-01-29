#ifndef AGNOCAST__NODE__TF2__STATIC_TRANSFORM_BROADCASTER_HPP_
#define AGNOCAST__NODE__TF2__STATIC_TRANSFORM_BROADCASTER_HPP_

#include "agnocast/agnocast.hpp"
#include "tf2_ros/qos.hpp"

#include "geometry_msgs/msg/transform_stamped.hpp"
#include "tf2_msgs/msg/tf_message.hpp"

#include <memory>
#include <vector>

namespace agnocast
{

/// \brief Broadcasts static transforms via Agnocast zero-copy IPC.
///
/// Static transforms are transforms that do not change over time (e.g., sensor mounts).
/// This class accumulates all static transforms and republishes them together,
/// using transient_local QoS to ensure late-joining subscribers receive all transforms.
class StaticTransformBroadcaster
{
public:
  /// \brief Constructor
  /// \param node Reference to an agnocast::Node
  /// \param qos QoS settings for the publisher (default: depth=1, transient_local)
  explicit StaticTransformBroadcaster(
    agnocast::Node & node, const rclcpp::QoS & qos = tf2_ros::StaticBroadcasterQoS());

  /// \brief Send a TransformStamped message
  /// The stamped data structure includes frame_id, and time, and parent_id already.  */
  void sendTransform(const geometry_msgs::msg::TransformStamped & transform);

  /// \brief Send a vector of TransformStamped messages
  /// The stamped data structure includes frame_id, and time, and parent_id already.  */
  void sendTransform(const std::vector<geometry_msgs::msg::TransformStamped> & transforms);

private:
  agnocast::Publisher<tf2_msgs::msg::TFMessage>::SharedPtr publisher_;
  tf2_msgs::msg::TFMessage net_message_;
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__STATIC_TRANSFORM_BROADCASTER_HPP_

#ifndef AGNOCAST__NODE__TF2__STATIC_TRANSFORM_BROADCASTER_HPP_
#define AGNOCAST__NODE__TF2__STATIC_TRANSFORM_BROADCASTER_HPP_

#include "agnocast/agnocast.hpp"

#include "geometry_msgs/msg/transform_stamped.hpp"
#include "tf2_msgs/msg/tf_message.hpp"

#include <memory>
#include <vector>

namespace agnocast
{

/// \brief Default QoS for static transform broadcasting (matches tf2_ros::StaticBroadcasterQoS)
///
/// Uses transient_local durability to ensure late-joining subscribers receive
/// previously published static transforms.
inline rclcpp::QoS StaticBroadcasterQoS(size_t depth = 1)
{
  return rclcpp::QoS(depth).transient_local();
}

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
    agnocast::Node & node, const rclcpp::QoS & qos = StaticBroadcasterQoS());

  /// \brief Send a single TransformStamped message
  ///
  /// If a transform with the same child_frame_id already exists, it will be updated.
  /// \param transform The transform to send
  void sendTransform(const geometry_msgs::msg::TransformStamped & transform);

  /// \brief Send a vector of TransformStamped messages
  /// \param transforms The transforms to send
  void sendTransform(const std::vector<geometry_msgs::msg::TransformStamped> & transforms);

private:
  agnocast::Publisher<tf2_msgs::msg::TFMessage>::SharedPtr publisher_;
  tf2_msgs::msg::TFMessage net_message_;  ///< Accumulated static transforms
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__STATIC_TRANSFORM_BROADCASTER_HPP_

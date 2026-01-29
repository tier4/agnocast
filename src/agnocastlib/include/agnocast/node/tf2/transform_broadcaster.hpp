#ifndef AGNOCAST__NODE__TF2__TRANSFORM_BROADCASTER_HPP_
#define AGNOCAST__NODE__TF2__TRANSFORM_BROADCASTER_HPP_

#include "agnocast/agnocast.hpp"
#include "tf2_ros/qos.hpp"

#include "geometry_msgs/msg/transform_stamped.hpp"
#include "tf2_msgs/msg/tf_message.hpp"

#include <memory>
#include <vector>

namespace agnocast
{

/// \brief This class provides an easy way to publish coordinate frame transform information
/// using Agnocast's zero-copy shared memory transport.
class TransformBroadcaster
{
public:
  /// \brief Node Constructor
  explicit TransformBroadcaster(
    agnocast::Node & node, const rclcpp::QoS & qos = tf2_ros::DynamicBroadcasterQoS());

  /// \brief Send a single TransformStamped message
  ///
  /// The transform added is from `child_frame_id` to `header.frame_id`.
  /// \param transform The transform to send
  void sendTransform(const geometry_msgs::msg::TransformStamped & transform);

  /// \brief Send a vector of TransformStamped messages
  /// \param transforms The transforms to send
  void sendTransform(const std::vector<geometry_msgs::msg::TransformStamped> & transforms);

private:
  agnocast::Publisher<tf2_msgs::msg::TFMessage>::SharedPtr publisher_;
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__TRANSFORM_BROADCASTER_HPP_

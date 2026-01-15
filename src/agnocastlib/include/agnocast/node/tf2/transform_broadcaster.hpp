// Copyright 2024 The Agnocast Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef AGNOCAST__NODE__TF2__TRANSFORM_BROADCASTER_HPP_
#define AGNOCAST__NODE__TF2__TRANSFORM_BROADCASTER_HPP_

#include "agnocast/agnocast.hpp"

#include "geometry_msgs/msg/transform_stamped.hpp"
#include "tf2_msgs/msg/tf_message.hpp"

#include <memory>
#include <vector>

namespace agnocast
{

/// \brief Default QoS for dynamic transform broadcasting (matches tf2_ros::DynamicBroadcasterQoS)
inline rclcpp::QoS DynamicBroadcasterQoS(size_t depth = 100)
{
  return rclcpp::QoS(depth);
}

/// \brief Broadcasts dynamic transforms via Agnocast zero-copy IPC.
///
/// This class provides an easy way to publish coordinate frame transform information
/// using Agnocast's zero-copy shared memory transport, avoiding DDS overhead.
class TransformBroadcaster
{
public:
  /// \brief Constructor
  /// \param node Reference to an agnocast::Node
  /// \param qos QoS settings for the publisher (default: depth=100)
  explicit TransformBroadcaster(
    agnocast::Node & node, const rclcpp::QoS & qos = DynamicBroadcasterQoS());

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

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

#ifndef AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_
#define AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_

#include "agnocast/agnocast.hpp"
#include "agnocast/node/tf2/buffer.hpp"

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
/// zero-copy shared memory transport, and populates an agnocast::Buffer
/// with the received transforms.
///
/// The constructor automatically configures the buffer for use with Agnocast:
/// - Sets using_dedicated_thread to true (required for timeout-based lookups)
class TransformListener
{
public:
  /// \brief Constructor with agnocast::Buffer
  ///
  /// \param buffer The buffer to populate with received transforms.
  ///        The buffer will be automatically configured for Agnocast use.
  /// \param node Reference to an agnocast::Node
  /// \param qos QoS for /tf subscription (default: depth=100)
  /// \param static_qos QoS for /tf_static subscription (default: depth=100, transient_local)
  TransformListener(
    agnocast::Buffer & buffer, agnocast::Node & node,
    const rclcpp::QoS & qos = DynamicListenerQoS(),
    const rclcpp::QoS & static_qos = StaticListenerQoS());

  virtual ~TransformListener() = default;

private:
  /// \brief Callback for /tf and /tf_static messages
  void subscription_callback(
    agnocast::ipc_shared_ptr<tf2_msgs::msg::TFMessage> && msg, bool is_static);

  agnocast::Buffer & buffer_;
  agnocast::Subscription<tf2_msgs::msg::TFMessage>::SharedPtr tf_subscription_;
  agnocast::Subscription<tf2_msgs::msg::TFMessage>::SharedPtr tf_static_subscription_;

  static constexpr const char * kDefaultAuthority = "default_authority";
};

}  // namespace agnocast

#endif  // AGNOCAST__NODE__TF2__TRANSFORM_LISTENER_HPP_

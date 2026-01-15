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
      RCLCPP_ERROR(
        rclcpp::get_logger("agnocast.tf2"), "Failed to set transform: %s", ex.what());
    }
  }
}

}  // namespace agnocast

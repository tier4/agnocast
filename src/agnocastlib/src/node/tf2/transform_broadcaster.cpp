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

#include "agnocast/node/tf2/transform_broadcaster.hpp"

namespace agnocast
{

TransformBroadcaster::TransformBroadcaster(agnocast::Node & node, const rclcpp::QoS & qos)
: publisher_(node.create_publisher<tf2_msgs::msg::TFMessage>("/tf", qos))
{
}

void TransformBroadcaster::sendTransform(const geometry_msgs::msg::TransformStamped & transform)
{
  sendTransform(std::vector<geometry_msgs::msg::TransformStamped>{transform});
}

void TransformBroadcaster::sendTransform(
  const std::vector<geometry_msgs::msg::TransformStamped> & transforms)
{
  auto msg = publisher_->borrow_loaned_message();
  msg->transforms = transforms;
  publisher_->publish(std::move(msg));
}

}  // namespace agnocast

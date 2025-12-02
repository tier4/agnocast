// Copyright 2025 Agnocast Contributors
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

#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp_components/register_node_macro.hpp"

#include <iostream>

using std::placeholders::_1;

class NoRclcppComposableSubscriber : public agnocast::Node
{
  agnocast::Subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;

  void callback(
    const agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> & message)
  {
    RCLCPP_INFO(
      get_logger(), "I heard dynamic size array message with size: %zu", message->data.size());
  }

public:
  explicit NoRclcppComposableSubscriber(const rclcpp::NodeOptions & options)
  : agnocast::Node(options)
  {
    // Declare parameters with default values
    declare_parameter("topic_name", std::string("/my_topic"));
    declare_parameter("queue_size", int64_t(1));

    // Get parameter values
    std::string topic_name;
    int64_t queue_size;
    get_parameter("topic_name", topic_name);
    get_parameter("queue_size", queue_size);

    RCLCPP_INFO(
      get_logger(), "NoRclcppComposableSubscriber node (name=%s) started.", get_name().c_str());
    RCLCPP_INFO(get_logger(), "  topic_name: %s", topic_name.c_str());
    RCLCPP_INFO(get_logger(), "  queue_size: %ld", queue_size);

    auto group = create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    sub_dynamic_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      topic_name, static_cast<size_t>(queue_size),
      std::bind(&NoRclcppComposableSubscriber::callback, this, _1), agnocast_options);
  }
};

RCLCPP_COMPONENTS_REGISTER_NODE(NoRclcppComposableSubscriber)

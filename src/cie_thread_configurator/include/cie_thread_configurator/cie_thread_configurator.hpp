// Copyright 2024 The Agnocast Authors
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

#pragma once

#include "rclcpp/rclcpp.hpp"

#include "cie_config_msgs/msg/callback_group_info.hpp"

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace cie_thread_configurator
{

std::string create_callback_group_id(
  rclcpp::CallbackGroup::SharedPtr group, rclcpp::Node::SharedPtr node,
  const std::vector<std::string> & agnocast_topics);

std::string create_callback_group_id(
  rclcpp::CallbackGroup::SharedPtr group,
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node,
  const std::vector<std::string> & agnocast_topics);

// Caution: Do not call in parallel
// Caution: Must be called after rclcpp::init() called
rclcpp::Publisher<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr create_client_publisher();

// `publisher` is assumed to be the return value of create_client_publisher()
void publish_callback_group_info(
  const rclcpp::Publisher<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr & publisher,
  int64_t tid, const std::string & callback_group_id);

// Get hardware information from lscpu command
std::map<std::string, std::string> get_hardware_info();

}  // namespace cie_thread_configurator

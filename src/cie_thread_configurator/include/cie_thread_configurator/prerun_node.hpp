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
#include "yaml-cpp/yaml.h"

#include "cie_config_msgs/msg/callback_group_info.hpp"

#include <filesystem>
#include <set>
#include <string>

class PrerunNode : public rclcpp::Node
{
public:
  PrerunNode();
  void dump_yaml_config(std::filesystem::path path);

private:
  void topic_callback(const cie_config_msgs::msg::CallbackGroupInfo::SharedPtr msg);

  rclcpp::Subscription<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr subscription_;
  std::set<std::string> callback_group_ids_;
};

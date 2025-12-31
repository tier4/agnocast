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

#include <string>
#include <unordered_map>
#include <vector>

class ThreadConfiguratorNode : public rclcpp::Node
{
  struct CallbackGroupConfig
  {
    std::string callback_group_id;
    int64_t thread_id = -1;
    std::vector<int> affinity;
    std::string policy;
    int priority;

    // For SCHED_DEADLINE
    unsigned int runtime;
    unsigned int period;
    unsigned int deadline;

    bool applied = false;
  };

public:
  explicit ThreadConfiguratorNode(const YAML::Node & yaml);
  ~ThreadConfiguratorNode();
  bool all_applied();
  void print_all_unapplied();

  bool exist_deadline_config();
  bool apply_deadline_configs();

private:
  bool set_affinity_by_cgroup(int64_t thread_id, const std::vector<int> & cpus);
  bool issue_syscalls(const CallbackGroupConfig & config);
  void topic_callback(const cie_config_msgs::msg::CallbackGroupInfo::SharedPtr msg);

  rclcpp::Subscription<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr subscription_;

  std::vector<CallbackGroupConfig> callback_group_configs_;
  std::unordered_map<std::string, CallbackGroupConfig *> id_to_callback_group_config_;
  int unapplied_num_;
  int cgroup_num_;

  std::vector<CallbackGroupConfig *> deadline_configs_;
};

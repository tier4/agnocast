#pragma once

#include "agnocast/agnocast.hpp"
#include "yaml-cpp/yaml.h"

#include "cie_config_msgs/msg/callback_group_info.hpp"

#include <filesystem>
#include <set>
#include <string>

class PrerunNode : public agnocast::Node
{
public:
  PrerunNode();
  void dump_yaml_config(std::filesystem::path path);

private:
  void topic_callback(
    const agnocast::ipc_shared_ptr<cie_config_msgs::msg::CallbackGroupInfo> & msg);

  agnocast::Subscription<cie_config_msgs::msg::CallbackGroupInfo>::SharedPtr subscription_;
  std::set<std::string> callback_group_ids_;
};

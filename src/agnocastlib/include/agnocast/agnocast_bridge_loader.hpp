#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <map>
#include <memory>
#include <string>
#include <utility>

namespace agnocast
{

using BridgeFn = std::shared_ptr<void> (*)(rclcpp::Node::SharedPtr, const BridgeTargetInfo &);

class BridgeLoader
{
public:
  BridgeLoader(rclcpp::Logger logger);
  ~BridgeLoader();

  std::shared_ptr<void> load_and_create(
    const MqMsgBridge & req, const std::string & unique_key, rclcpp::Node::SharedPtr node);

private:
  std::pair<void *, uintptr_t> load_library_base(const char * lib_path, const char * symbol_name);

  std::pair<BridgeFn, std::shared_ptr<void>> resolve_factory_function(
    const MqMsgBridge & req, const std::string & unique_key);

  std::shared_ptr<void> create_bridge_instance(
    BridgeFn entry_func, std::shared_ptr<void> lib_handle, rclcpp::Node::SharedPtr node,
    const BridgeTargetInfo & target);

  rclcpp::Logger logger_;

  std::map<std::string, std::pair<BridgeFn, std::shared_ptr<void>>> cached_factories_;
};

}  // namespace agnocast

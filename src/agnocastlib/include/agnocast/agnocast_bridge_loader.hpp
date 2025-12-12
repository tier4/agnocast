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
  explicit BridgeLoader(const rclcpp::Logger & logger);
  ~BridgeLoader();

  BridgeLoader(const BridgeLoader &) = delete;
  BridgeLoader & operator=(const BridgeLoader &) = delete;

  // NOLINT(readability-convert-member-functions-to-static)
  std::shared_ptr<void> create(
    const MqMsgBridge & req, const std::string & topic_name_with_direction,
    const rclcpp::Node::SharedPtr & node);

private:
  rclcpp::Logger logger_;

  std::map<std::string, std::pair<BridgeFn, std::shared_ptr<void>>> cached_factories_;

  std::pair<void *, uintptr_t> load_library(const char * lib_path, const char * symbol_name);
  std::pair<BridgeFn, std::shared_ptr<void>> resolve_factory_function(
    const MqMsgBridge & req, const std::string & unique_key);
};

}  // namespace agnocast

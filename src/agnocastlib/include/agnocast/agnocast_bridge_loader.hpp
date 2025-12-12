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

  std::shared_ptr<void> create(
    const MqMsgBridge & req, const std::string & topic_name_with_direction,
    const rclcpp::Node::SharedPtr &
      node);  // NOLINT(readability-convert-member-functions-to-static)

private:
  rclcpp::Logger logger_;

  std::map<std::string, std::pair<BridgeFn, std::shared_ptr<void>>> cached_factories_;
};

}  // namespace agnocast

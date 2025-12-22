#include "agnocast/agnocast_bridge_config_p.hpp"

#include <rclcpp/logging.hpp>

namespace agnocast
{

BridgeConfigP::BridgeConfigP(const rclcpp::Logger & logger) : logger_(logger)
{
  RCLCPP_INFO(logger_, "BridgeConfigP initialized (Skeleton).");
}

BridgeConfigP::~BridgeConfigP()
{
}

}  // namespace agnocast
#include "agnocast/agnocast_bridge_loader.hpp"

namespace agnocast
{

BridgeLoader::BridgeLoader(rclcpp::Logger logger) : logger_(logger)
{
}

BridgeLoader::~BridgeLoader()
{
  cached_factories_.clear();
}

}  // namespace agnocast

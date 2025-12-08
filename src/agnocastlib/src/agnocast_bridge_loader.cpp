#include "agnocast/agnocast_bridge_loader.hpp"

#include <dlfcn.h>
#include <link.h>

#include <cstring>
#include <stdexcept>

namespace agnocast
{

BridgeLoader::BridgeLoader(rclcpp::Logger logger) : logger_(logger)
{
}

BridgeLoader::~BridgeLoader()
{
  cached_factories_.clear();
}

}
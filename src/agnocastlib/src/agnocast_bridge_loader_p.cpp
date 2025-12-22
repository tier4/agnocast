#include "agnocast/agnocast_bridge_loader_p.hpp"

#include "agnocast/agnocast_utils.hpp"

#include <dlfcn.h>
#include <elf.h>
#include <link.h>

#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <utility>

namespace agnocast
{

BridgeLoaderP::BridgeLoaderP(const rclcpp::Logger & logger) : logger_(logger)
{
  RCLCPP_INFO(logger_, "BridgeLoaderP initialized (Skeleton).");
}

BridgeLoaderP::~BridgeLoaderP()
{
  // cached_factories_.clear();
}

}  // namespace agnocast
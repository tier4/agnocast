#include "agnocast/agnocast_bridge_ipc_event_loop_p.hpp"

#include <rclcpp/logging.hpp>

namespace agnocast
{

BridgeIpcEventLoopP::BridgeIpcEventLoopP(const rclcpp::Logger & logger) : logger_(logger)
{
  RCLCPP_INFO(logger_, "BridgeIpcEventLoopP initialized (Skeleton).");
}

BridgeIpcEventLoopP::~BridgeIpcEventLoopP()
{
}

void BridgeIpcEventLoopP::spin_once()
{
}

}  // namespace agnocast
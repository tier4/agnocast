#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"

namespace agnocast
{

BridgeIpcEventLoop::BridgeIpcEventLoop(pid_t /*target_pid*/, rclcpp::Logger logger)
: logger_(logger)
{
}

BridgeIpcEventLoop::~BridgeIpcEventLoop()
{
}

}  // namespace agnocast

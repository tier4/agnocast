#pragma once

#include "agnocast/agnocast_bridge_config_p.hpp"
#include "agnocast/agnocast_bridge_ipc_event_loop_p.hpp"
#include "agnocast/agnocast_bridge_loader_p.hpp"

#include <rclcpp/rclcpp.hpp>

namespace agnocast
{

class PerformanceBridgeManager
{
public:
  PerformanceBridgeManager();
  ~PerformanceBridgeManager();

  void run();

private:
  rclcpp::Logger logger_;
  BridgeIpcEventLoopP event_loop_;
  BridgeLoaderP loader_;
  BridgeConfigP config_;
};

}  // namespace agnocast
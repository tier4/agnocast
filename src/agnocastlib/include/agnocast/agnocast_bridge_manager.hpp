#pragma once

#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"
#include "agnocast/agnocast_bridge_loader.hpp"
#include "rclcpp/rclcpp.hpp"

#include <memory>

namespace agnocast
{

class BridgeManager
{
public:
  explicit BridgeManager(pid_t target_pid);
  ~BridgeManager();

  BridgeManager(const BridgeManager &) = delete;
  BridgeManager & operator=(const BridgeManager &) = delete;

private:
  const pid_t target_pid_;
  rclcpp::Logger logger_;

  BridgeIpcEventLoop event_loop_;
  BridgeLoader loader_;
};

}  // namespace agnocast

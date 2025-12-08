#pragma once

#include <rclcpp/logger.hpp>

#include <sys/types.h>

namespace agnocast
{

class BridgeIpcEventLoop
{
public:
  BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger logger);
  ~BridgeIpcEventLoop() = default;

  BridgeIpcEventLoop(const BridgeIpcEventLoop &) = delete;
  BridgeIpcEventLoop & operator=(const BridgeIpcEventLoop &) = delete;

private:
  rclcpp::Logger logger_;
};

}  // namespace agnocast

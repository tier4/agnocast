#pragma once

#include <rclcpp/logger.hpp>

#include <sys/types.h>

namespace agnocast
{

class BridgeIpcEventLoop
{
public:
  BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger & logger);
  ~BridgeIpcEventLoop();

  BridgeIpcEventLoop(const BridgeIpcEventLoop &) = delete;
  BridgeIpcEventLoop & operator=(const BridgeIpcEventLoop &) = delete;

  bool spin_once(int timeout_ms);

private:
  rclcpp::Logger logger_;

  int epoll_fd_ = -1;

  void setup_epoll();
};

}  // namespace agnocast

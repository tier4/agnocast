#pragma once

#include <rclcpp/logger.hpp>

namespace agnocast
{

class BridgeIpcEventLoopP
{
public:
  explicit BridgeIpcEventLoopP(const rclcpp::Logger & logger);
  ~BridgeIpcEventLoopP();

  void spin_once();

private:
  rclcpp::Logger logger_;
};

}  // namespace agnocast

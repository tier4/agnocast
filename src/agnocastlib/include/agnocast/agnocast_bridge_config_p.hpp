#pragma once

#include <rclcpp/logger.hpp>

namespace agnocast
{

class BridgeConfigP
{
public:
  explicit BridgeConfigP(const rclcpp::Logger & logger);
  ~BridgeConfigP();

  // void load_config();

private:
  rclcpp::Logger logger_;
};

}  // namespace agnocast
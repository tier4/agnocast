#pragma once

#include <rclcpp/logger.hpp>

namespace agnocast
{

class PerformanceBridgeConfig
{
public:
  explicit PerformanceBridgeConfig(const rclcpp::Logger & logger);
  ~PerformanceBridgeConfig();

  // void load_config();

private:
  rclcpp::Logger logger_;
};

}  // namespace agnocast

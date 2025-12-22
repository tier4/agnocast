#pragma once

#include <rclcpp/logger.hpp>

#include <memory>
#include <string>
#include <unordered_map>

namespace agnocast
{

class BridgeLoaderP
{
public:
  explicit BridgeLoaderP(const rclcpp::Logger & logger);
  ~BridgeLoaderP();

  // void load_library(const std::string & path);

private:
  rclcpp::Logger logger_;

  // std::unordered_map<std::string, void *> cached_factories_;
};

}  // namespace agnocast

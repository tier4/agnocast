#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <utility>

namespace agnocast
{

using BridgeFn = std::shared_ptr<void> (*)(rclcpp::Node::SharedPtr, const BridgeTargetInfo &);

class BridgeLoader
{
public:
  explicit BridgeLoader(const rclcpp::Logger & logger);
  ~BridgeLoader();

  BridgeLoader(const BridgeLoader &) = delete;
  BridgeLoader & operator=(const BridgeLoader &) = delete;

private:
  rclcpp::Logger logger_;

  std::map<std::string, std::pair<BridgeFn, std::shared_ptr<void>>> cached_factories_;

  std::pair<void *, uintptr_t> load_library_base(const char * lib_path, const char * symbol_name);
};

}  // namespace agnocast

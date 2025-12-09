#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"

#include "agnocast/agnocast_bridge_loader.hpp"

#include <dlfcn.h>
#include <link.h>

#include <cstring>
#include <stdexcept>

namespace agnocast
{

BridgeLoader::BridgeLoader(const rclcpp::Logger & logger) : logger_(logger)
{
}

BridgeLoader::~BridgeLoader()
{
  cached_factories_.clear();
}

std::shared_ptr<void> BridgeLoader::load_and_create(
  const MqMsgBridge & req, const std::string & unique_key, rclcpp::Node::SharedPtr node)
{
  auto [entry_func, lib_handle] = resolve_factory_function(req, unique_key);

  if (!entry_func) {
    // TODO: Output error log and return
    return nullptr;
  }

  return create_bridge_instance(entry_func, lib_handle, node, req.target);
}

std::pair<void *, uintptr_t> BridgeLoader::load_library_base(
  const char * lib_path, const char * symbol_name)
{
  // TODO: Logic for loading the library via dlopen/dlinfo and retrieving the base address.
  return {nullptr, 0};
}

std::pair<BridgeFn, std::shared_ptr<void>> BridgeLoader::resolve_factory_function(
  const MqMsgBridge & req, const std::string & unique_key)
{
  // TODO: Cache check logic

  // TODO: Call load_library_base to get the raw handle and base address
  auto [raw_handle, base_addr] =
    load_library_base(req.factory.shared_lib_path, req.factory.symbol_name);

  (void)raw_handle;
  (void)base_addr;

  // TODO: Logic to calculate the function pointer from base address and offset, and cache it.

  return {nullptr, nullptr};
}

std::shared_ptr<void> BridgeLoader::create_bridge_instance(
  BridgeFn entry_func, std::shared_ptr<void> lib_handle, rclcpp::Node::SharedPtr node,
  const BridgeTargetInfo & target)
{
  // TODO: Logic to call the factory function (entry_func) and create the bridge.
  // TODO: Logic to manage the ownership of the created bridge instance and the library handle.
  return nullptr;
}

}  // namespace agnocast

#pragma GCC diagnostic pop

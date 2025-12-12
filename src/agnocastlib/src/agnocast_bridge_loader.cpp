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

// NOLINTNEXTLINE(readability-convert-member-functions-to-static)
std::shared_ptr<void> BridgeLoader::create(
  const MqMsgBridge & req, const std::string & topic_name_with_direction,
  const rclcpp::Node::SharedPtr & node)
{
  (void)node;  // TODO(yutarokobayashi): Remove

  auto [entry_func, lib_handle] = resolve_factory_function(req, topic_name_with_direction);

  if (!entry_func) {
    const char * err = dlerror();
    RCLCPP_ERROR(
      logger_, "Failed to resolve factory for '%s': %s", topic_name_with_direction.c_str(),
      err ? err : "Unknown error");
    return nullptr;
  }

  return nullptr;  // TODO(yutarokobayashi): Invoke the factory function and return the instance.
}

std::pair<void *, uintptr_t> BridgeLoader::load_library(
  const char * /*lib_path*/, const char * /*symbol_name*/)
{
  // TODO: Implement library loading and base address retrieval.
  // This function should:
  // - Open the specified library (or main executable) via dlopen.
  // - Query the link map (dlinfo) to find the runtime load address.
  // - Return the handle and base address, or a null pair on failure.
  return {nullptr, 0};
}

std::pair<BridgeFn, std::shared_ptr<void>> BridgeLoader::resolve_factory_function(
  const MqMsgBridge & req, const std::string & topic_name_with_direction)
{
  if (auto it = cached_factories_.find(topic_name_with_direction); it != cached_factories_.end()) {
    // Return the cached pair of the factory function and the shared library handle.
    return it->second;
  }

  dlerror();
  auto [raw_handle, base_addr] = load_library(req.factory.shared_lib_path, req.factory.symbol_name);

  if (!raw_handle || (base_addr == 0 && req.factory.fn_offset == 0)) {
    if (raw_handle) {
      dlclose(raw_handle);
    }
    return {nullptr, nullptr};
  }

  // Manage Handle Lifecycle
  std::shared_ptr<void> lib_handle_ptr(raw_handle, [](void * h) {
    if (h) dlclose(h);
  });

  // Resolve Main Function
  auto entry_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset);
  cached_factories_[topic_name_with_direction] = {entry_func, lib_handle_ptr};

  // Register Reverse Function
  if (req.factory.fn_offset_reverse != 0) {
    const char * suffix = (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_A2R" : "_R2A";
    std::string reverse_key = std::string(req.target.topic_name) + suffix;

    auto reverse_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset_reverse);
    cached_factories_[reverse_key] = {reverse_func, lib_handle_ptr};
  }

  return {entry_func, lib_handle_ptr};
}

}  // namespace agnocast

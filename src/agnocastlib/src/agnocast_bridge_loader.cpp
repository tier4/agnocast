#include "agnocast/agnocast_bridge_loader.hpp"

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
    const char * err = dlerror();
    RCLCPP_ERROR(
      logger_, "Failed to resolve factory for '%s': %s", unique_key.c_str(),
      err ? err : "Unknown error");
    return nullptr;
  }

  return create_bridge_instance(entry_func, lib_handle, node, req.target);
}

std::pair<void * (*)(), void *> BridgeLoader::resolve_factory_function(
  const MqMsgBridge & req, const std::string & unique_key)
{
  (void)req;         // TODO(yutarokobayashi): Remove
  (void)unique_key;  // TODO(yutarokobayashi): Remove

  // TODO(yutarokobayashi): Implement dynamic library loading (dlopen/dlsym)

  return {nullptr, nullptr};
}

std::shared_ptr<void> BridgeLoader::create_bridge_instance(
  void * (*entry_func)(), void * lib_handle, rclcpp::Node::SharedPtr node,
  const std::string & target)
{
  (void)entry_func;  // TODO(yutarokobayashi): Remove
  (void)lib_handle;  // TODO(yutarokobayashi): Remove
  (void)node;        // TODO(yutarokobayashi): Remove
  (void)target;      // TODO(yutarokobayashi): Remove

  return nullptr;
}

}  // namespace agnocast

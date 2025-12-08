#include "agnocast/agnocast_bridge_loader.hpp"

#include <dlfcn.h>
#include <link.h>

#include <cstring>
#include <stdexcept>

namespace agnocast
{

BridgeLoader::BridgeLoader(rclcpp::Logger logger) : logger_(logger)
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

std::pair<void *, uintptr_t> BridgeLoader::load_library_base(
  const char * lib_path, const char * symbol_name)
{
  void * handle = nullptr;

  if (std::strcmp(symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    handle = dlopen(NULL, RTLD_NOW);
  } else {
    // RTLD_LOCAL を推奨
    handle = dlopen(lib_path, RTLD_NOW | RTLD_LOCAL);
  }

  if (!handle) {
    return {nullptr, 0};
  }

  // struct link_map * map = static_cast<struct link_map *>(handle);
  struct link_map * map = nullptr;
  if (dlinfo(handle, RTLD_DI_LINKMAP, &map) != 0) {
    // dlinfoに失敗した場合はハンドルを閉じてエラーを返す
    // (通常ここに来ることは稀ですが、安全性のため)
    dlclose(handle);
    return {nullptr, 0};
  }
  return {handle, map->l_addr};
}

std::pair<BridgeFn, std::shared_ptr<void>> BridgeLoader::resolve_factory_function(
  const MqMsgBridge & req, const std::string & unique_key)
{
  auto it = cached_factories_.find(unique_key);
  if (it != cached_factories_.end()) {
    RCLCPP_INFO(logger_, "Cache hit for '%s'", unique_key.c_str());
    return it->second;
  }

  dlerror();
  auto [raw_handle, base_addr] =
    load_library_base(req.factory.shared_lib_path, req.factory.symbol_name);

  if (base_addr == 0 && req.factory.fn_offset == 0) {
    if (raw_handle) dlclose(raw_handle);
    return {nullptr, nullptr};
  }

  std::shared_ptr<void> lib_handle_ptr;
  if (raw_handle) {
    lib_handle_ptr.reset(raw_handle, [](void * h) {
      if (h) dlclose(h);
    });
  }

  BridgeFn entry_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset);

  cached_factories_[unique_key] = {entry_func, lib_handle_ptr};

  if (req.factory.fn_offset_reverse != 0) {
    std::string topic_name = req.target.topic_name;
    std::string reverse_key =
      topic_name + ((req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_A2R" : "_R2A");

    BridgeFn reverse_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset_reverse);
    cached_factories_[reverse_key] = {reverse_func, lib_handle_ptr};
  }

  return {entry_func, lib_handle_ptr};
}

std::shared_ptr<void> BridgeLoader::create_bridge_instance(
  BridgeFn entry_func, std::shared_ptr<void> lib_handle, rclcpp::Node::SharedPtr node,
  const BridgeTargetInfo & target)
{
  try {
    auto bridge_resource = entry_func(node, target);
    if (!bridge_resource) return nullptr;

    if (lib_handle) {
      using BundleType = std::pair<std::shared_ptr<void>, std::shared_ptr<void>>;
      auto bundle = std::make_shared<BundleType>(lib_handle, bridge_resource);
      return std::shared_ptr<void>(bundle, bridge_resource.get());
    } else {
      return bridge_resource;
    }
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "Exception in factory: %s", e.what());
    return nullptr;
  }
}

}  // namespace agnocast

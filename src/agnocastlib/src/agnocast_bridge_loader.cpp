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
  const MqMsgBridge & req, const std::string & topic_name_with_direction)
{
  auto it = cached_factories_.find(topic_name_with_direction);
  if (it != cached_factories_.end()) {
    RCLCPP_INFO(logger_, "Cache hit for '%s'", topic_name_with_direction.c_str());
    return it->second;
  }

  dlerror();
  auto [raw_handle, base_addr] =
    load_library_base(req.factory.shared_lib_path, req.factory.symbol_name);

  if (base_addr == 0 && req.factory.fn_offset == 0) {
    if (raw_handle) dlclose(raw_handle);
    return {nullptr, nullptr};
  }

  // Manage Handle Lifecycle
  std::shared_ptr<void> lib_handle_ptr(raw_handle, [](void * h) {
    if (h != nullptr) {
      dlclose(h);
    }
  });

  // Resolve Main Function
  uintptr_t entry_addr = base_addr + req.factory.fn_offset;
  BridgeFn entry_func = nullptr;

  if (is_address_in_library_code_segment(raw_handle, entry_addr)) {
    entry_func = reinterpret_cast<BridgeFn>(entry_addr);
  } else {
    RCLCPP_ERROR(
      logger_, "Main factory function pointer for '%s' is out of bounds: 0x%lx",
      topic_name_with_direction.c_str(), static_cast<unsigned long>(entry_addr));
    return {nullptr, nullptr};
  }

  // Register Reverse Function
  const char * suffix = (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_A2R" : "_R2A";
  std::string topic_name_with_reverse = std::string(req.target.topic_name) + suffix;

  uintptr_t reverse_addr = base_addr + req.factory.fn_offset_reverse;
  BridgeFn reverse_func = nullptr;

  if (is_address_in_library_code_segment(raw_handle, reverse_addr)) {
    reverse_func = reinterpret_cast<BridgeFn>(reverse_addr);
  } else {
    RCLCPP_ERROR(
      logger_, "Reverse function pointer for '%s' is out of bounds: 0x%lx",
      topic_name_with_reverse.c_str(), static_cast<unsigned long>(reverse_addr));
    return {nullptr, nullptr};
  }

  cached_factories_[topic_name_with_direction] = {entry_func, lib_handle_ptr};
  cached_factories_[topic_name_with_reverse] = {reverse_func, lib_handle_ptr};

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

bool BridgeLoader::is_address_in_library_code_segment(void * handle, uintptr_t addr)
{
  struct link_map * lm = nullptr;
  if (dlinfo(handle, RTLD_DI_LINKMAP, &lm) != 0 || lm == nullptr) {
    return false;
  }

  ElfW(Addr) base = lm->l_addr;
  ElfW(Ehdr) * ehdr = reinterpret_cast<ElfW(Ehdr) *>(base);
  ElfW(Phdr) * phdr = reinterpret_cast<ElfW(Phdr) *>(base + ehdr->e_phoff);
  for (int i = 0; i < ehdr->e_phnum; ++i) {
    if (phdr[i].p_type == PT_LOAD && (phdr[i].p_flags & PF_X)) {
      uintptr_t seg_start = base + phdr[i].p_vaddr;
      uintptr_t seg_end = seg_start + phdr[i].p_memsz;
      if (addr >= seg_start && addr < seg_end) {
        return true;
      }
    }
  }
  return false;
}

}  // namespace agnocast

#include "agnocast/agnocast_bridge_loader.hpp"

#include <dlfcn.h>
#include <elf.h>
#include <link.h>

#include <cstdint>  // uintptr_t
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

  if (entry_func == nullptr) {
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
  // TODO(yutarokobayashi): Implement library loading and base address retrieval.
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

  // Clear any existing dynamic linker error state before loading the library and resolving the
  // symbol. This ensures that a subsequent call to dlerror() will report only errors that occurred
  // after this point.
  dlerror();
  auto [raw_handle, base_addr] = load_library(
    static_cast<const char *>(req.factory.shared_lib_path),
    static_cast<const char *>(req.factory.symbol_name));

  if ((raw_handle == nullptr) || (base_addr == 0)) {
    if (raw_handle != nullptr) {
      dlclose(raw_handle);
    }
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
  std::string topic_name_with_reverse =
    std::string(static_cast<const char *>(req.target.topic_name)) + suffix;

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

bool BridgeLoader::is_address_in_library_code_segment(void * handle, uintptr_t addr)
{
  struct link_map * lm = nullptr;
  if (dlinfo(handle, RTLD_DI_LINKMAP, &lm) != 0 || lm == nullptr) {
    return false;
  }

  const auto base = static_cast<uintptr_t>(lm->l_addr);
  const auto * ehdr = reinterpret_cast<const ElfW(Ehdr) *>(base);
  const auto * phdr = reinterpret_cast<const ElfW(Phdr) *>(base + ehdr->e_phoff);

  for (int i = 0; i < ehdr->e_phnum; ++i) {
    const auto & segment = phdr[i];  // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
    const auto flags = segment.p_flags;
    constexpr auto exec_flag = static_cast<ElfW(Word)>(PF_X);

    if (segment.p_type == PT_LOAD && ((flags & exec_flag) != 0U)) {
      const uintptr_t seg_start = base + segment.p_vaddr;
      const uintptr_t seg_end = seg_start + segment.p_memsz;

      if (addr >= seg_start && addr < seg_end) {
        return true;
      }
    }
  }
  return false;
}

}  // namespace agnocast

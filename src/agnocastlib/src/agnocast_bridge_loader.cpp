#include "agnocast/agnocast_bridge_loader.hpp"

#include <dlfcn.h>
#include <link.h>

#include <cstring>

namespace agnocast
{

BridgeLoader::BridgeLoader(const rclcpp::Logger & logger) : logger_(logger)
{
}

BridgeLoader::~BridgeLoader()
{
  cached_factories_.clear();
}

std::pair<void *, uintptr_t> BridgeLoader::load_library_base(
  const char * lib_path, const char * symbol_name)
{
  void * handle = nullptr;

  if (std::strcmp(symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    handle = dlopen(NULL, RTLD_NOW);
  } else {
    handle = dlopen(lib_path, RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND);
  }

  if (!handle) {
    return {nullptr, 0};
  }

  struct link_map * map = nullptr;
  if (dlinfo(handle, RTLD_DI_LINKMAP, &map) == -1 || !map) {
    dlclose(handle);
    return {nullptr, 0};
  }

  return {handle, map->l_addr};
}

}  // namespace agnocast

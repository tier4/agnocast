#include "agnocast/agnocast_bridge_loader_p.hpp"

#include <ament_index_cpp/get_package_prefix.hpp>  // 追加

#include <dlfcn.h>

#include <algorithm>

namespace agnocast
{

BridgeLoaderP::BridgeLoaderP(const rclcpp::Logger & logger) : logger_(logger)
{
}

BridgeLoaderP::~BridgeLoaderP()
{
  for (auto & pair : loaded_libraries_) {
    if (pair.second) {
      dlclose(pair.second);
    }
  }
  loaded_libraries_.clear();
}

std::string BridgeLoaderP::convert_type_to_snake_case(const std::string & message_type) const
{
  std::string result = message_type;
  std::replace(result.begin(), result.end(), '/', '_');
  return result;
}

std::string BridgeLoaderP::generate_library_path(
  const std::string & snake_type, const std::string & plugin_suffix) const
{
  try {
    const std::string package_prefix = ament_index_cpp::get_package_prefix("agnocastlib");

    // パス生成ルール: prefix + /lib/agnocastlib/bridge_plugins/lib{suffix}_bridge_plugin_{type}.so
    return package_prefix + "/lib/agnocastlib/bridge_plugins/lib" + plugin_suffix +
           "_bridge_plugin_" + snake_type + ".so";

  } catch (const ament_index_cpp::PackageNotFoundError & e) {
    RCLCPP_ERROR(
      logger_, "Could not find package 'agnocastlib' to locate plugins. Error: %s", e.what());
    return "";
  }
}

void * BridgeLoaderP::load_library(const std::string & library_path)
{
  if (library_path.empty()) return nullptr;

  if (loaded_libraries_.find(library_path) != loaded_libraries_.end()) {
    return loaded_libraries_[library_path];
  }

  // RTLD_LAZY でロード (元のコードと同じ)
  void * handle = dlopen(library_path.c_str(), RTLD_LAZY);

  if (!handle) {
    RCLCPP_ERROR(logger_, "Failed to load plugin '%s'. Error: %s", library_path.c_str(), dlerror());
    return nullptr;
  }

  RCLCPP_INFO(logger_, "Loaded plugin: %s", library_path.c_str());
  loaded_libraries_[library_path] = handle;
  return handle;
}

// ---------------------------------------------------------------------------
// R2A Creation
// ---------------------------------------------------------------------------
rclcpp::SubscriptionBase::SharedPtr BridgeLoaderP::create_r2a_bridge(
  rclcpp::Node::SharedPtr node, const std::string & topic_name, const std::string & message_type,
  const rclcpp::QoS & qos)
{
  std::string snake_type = convert_type_to_snake_case(message_type);
  std::string lib_path = generate_library_path(snake_type, "r2a");

  void * handle = load_library(lib_path);
  if (!handle) return nullptr;

  auto factory = reinterpret_cast<BridgeEntryR2A>(dlsym(handle, "create_r2a_bridge"));

  const char * dlsym_error = dlerror();
  if (!factory || dlsym_error != nullptr) {
    RCLCPP_ERROR(
      logger_, "Failed to find symbol 'create_r2a_bridge' in %s: %s", lib_path.c_str(),
      dlsym_error ? dlsym_error : "Unknown error");
    return nullptr;
  }

  RCLCPP_INFO(logger_, "Creating R2A bridge for topic: %s", topic_name.c_str());
  return factory(node, topic_name, qos);
}

// ---------------------------------------------------------------------------
// A2R Creation
// ---------------------------------------------------------------------------
std::shared_ptr<agnocast::SubscriptionBase> BridgeLoaderP::create_a2r_bridge(
  rclcpp::Node::SharedPtr node, const std::string & topic_name, const std::string & message_type,
  const rclcpp::QoS & qos)
{
  std::string snake_type = convert_type_to_snake_case(message_type);
  std::string lib_path = generate_library_path(snake_type, "a2r");

  void * handle = load_library(lib_path);
  if (!handle) return nullptr;

  auto factory = reinterpret_cast<BridgeEntryA2R>(dlsym(handle, "create_a2r_bridge"));

  const char * dlsym_error = dlerror();
  if (!factory || dlsym_error != nullptr) {
    RCLCPP_ERROR(
      logger_, "Failed to find symbol 'create_a2r_bridge' in %s: %s", lib_path.c_str(),
      dlsym_error ? dlsym_error : "Unknown error");
    return nullptr;
  }

  RCLCPP_INFO(logger_, "Creating A2R bridge for topic: %s", topic_name.c_str());
  return factory(node, topic_name, qos);
}

}  // namespace agnocast

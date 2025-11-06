#pragma once

#include "agnocast/agnocast_bridge_types.hpp"
#include "agnocast/agnocast_mq.hpp"

#include <ament_index_cpp/get_package_prefix.hpp>
#include <rclcpp/rclcpp.hpp>

#include <dlfcn.h>
#include <mqueue.h>

#include <atomic>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

namespace agnocast
{

extern int agnocast_fd;

class BridgeManager
{
public:
  BridgeManager();
  ~BridgeManager();
  void run();

private:
  std::vector<ActiveBridgeR2A> active_r2a_bridges_;
  std::vector<ActiveBridgeA2R> active_a2r_bridges_;
  std::vector<std::thread> worker_threads_;
  std::mutex bridge_mutex_;
  BridgeConfig bridge_config_;

  rclcpp::Node::SharedPtr node_;
  rclcpp::Logger logger_;
  std::unique_ptr<rclcpp::Executor> executor_;
  std::thread spin_thread_;

  mqd_t mq_;
  int epoll_fd_;
  std::string mq_name_str_;

  void launch_r2a_bridge_thread(const BridgeRequest & request);
  void launch_a2r_bridge_thread(const BridgeRequest & request);
  void handle_bridge_request();
  void reload_and_update_bridges();

  void check_and_shutdown_idle_bridges();
  void check_and_shutdown_daemon_if_idle();
  void shutdown_manager_internal();

  BridgeConfig parse_bridge_config();
  std::unique_ptr<rclcpp::Executor> select_executor();

  static std::atomic<bool> reload_filter_request_;
  static void sighup_handler(int signum);

  template <typename ActiveBridgeT, typename CreateFuncT, typename SubscriptionT>
  void load_and_launch_plugin(
    const BridgeRequest & request, std::vector<ActiveBridgeT> & active_bridges_vec,
    const std::string & plugin_suffix, const std::string & symbol_name)
  {
    std::string plugin_path;
    try {
      const std::string package_prefix = ament_index_cpp::get_package_prefix("agnocastlib");

      std::string type_name = request.message_type;
      std::replace(type_name.begin(), type_name.end(), '/', '_');

      plugin_path = package_prefix + "/lib/agnocastlib/bridge_plugins/lib" + plugin_suffix +
                    "_bridge_plugin_" + type_name + ".so";

    } catch (const ament_index_cpp::PackageNotFoundError & e) {
      RCLCPP_ERROR(
        this->logger_, "Could not find package 'agnocastlib' to locate plugins. Error: %s",
        e.what());
      return;
    }

    void * handle = dlopen(plugin_path.c_str(), RTLD_LAZY);
    if (!handle) {
      RCLCPP_ERROR(
        this->logger_, "[BRIDGE THREAD] Failed to load plugin '%s'. Error: %s", plugin_path.c_str(),
        dlerror());
      return;
    }

    CreateFuncT create_bridge_ptr =
      reinterpret_cast<CreateFuncT>(dlsym(handle, symbol_name.c_str()));

    const char * dlsym_error = dlerror();
    if (dlsym_error != nullptr) {
      dlclose(handle);
      return;
    }

    SubscriptionT subscription =
      create_bridge_ptr(this->node_, std::string(request.topic_name), rclcpp::QoS(10));

    if (subscription) {
      std::lock_guard<std::mutex> lock(this->bridge_mutex_);
      active_bridges_vec.push_back({request.topic_name, subscription, handle});
    } else {
      dlclose(handle);
    }
  }
};
}  // namespace agnocast
#pragma once

#include "agnocast/agnocast_bridge_types.hpp"
#include "agnocast/agnocast_mq.hpp"

#include <ament_index_cpp/get_package_prefix.hpp>
#include <rclcpp/rclcpp.hpp>

#include <dlfcn.h>
#include <mqueue.h>
#include <sys/ioctl.h>
#include <yaml-cpp/yaml.h>

#include <atomic>
#include <future>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

constexpr int DEFAULT_BRIDGE_QOS_DEPTH = 10;

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
  // ---------------------------------------------------------------------------
  // Static Members (Signal Handling)
  // ---------------------------------------------------------------------------
  static std::atomic<bool> reload_filter_request_;
  static void sighup_handler(int signum);

  // ---------------------------------------------------------------------------
  // Data Members (Core Components)
  // ---------------------------------------------------------------------------
  rclcpp::Node::SharedPtr node_;
  rclcpp::Logger logger_;
  BridgeConfig bridge_config_;  // Current filter configuration
  std::unique_ptr<rclcpp::Executor> executor_;
  std::thread spin_thread_;  // Thread for spinning the executor

  // ---------------------------------------------------------------------------
  // Data Members (State Management)
  // ---------------------------------------------------------------------------
  std::vector<ActiveBridgeR2A> active_r2a_bridges_;
  std::vector<ActiveBridgeA2R> active_a2r_bridges_;
  std::vector<std::future<void>> worker_futures_;  // Futures for bridge worker threads
  mutable std::mutex bridges_mutex_;               // Protects active bridge vectors
  std::string self_node_name_;

  // ---------------------------------------------------------------------------
  // Data Members (IPC / Event Monitoring)
  // ---------------------------------------------------------------------------
  mqd_t mq_;                 // POSIX Message Queue descriptor
  int epoll_fd_;             // epoll file descriptor
  std::string mq_name_str_;  // Message Queue name

  // ---------------------------------------------------------------------------
  // Initialization / Setup (Called from constructor)
  // ---------------------------------------------------------------------------
  void setup_message_queue();
  void setup_signal_handler();
  void setup_epoll();
  std::unique_ptr<rclcpp::Executor> select_executor();
  BridgeConfig parse_bridge_config();
  void parse_rules_node(const YAML::Node & rules, BridgeConfig & config);

  // ---------------------------------------------------------------------------
  // Main Loop Tasks (Called periodically from run())
  // ---------------------------------------------------------------------------
  void handle_bridge_request(const BridgeRequest & req);
  void reload_and_update_bridges();
  void discover_ros2_topics_for_allow_all();
  void check_and_remove_bridges();
  void check_and_request_rclcpp_shutdown();
  void cleanup_finished_futures();

  // ---------------------------------------------------------------------------
  // Bridge Creation (Async thread entry points)
  // ---------------------------------------------------------------------------
  void launch_r2a_bridge_thread(const BridgeRequest & request);
  void launch_a2r_bridge_thread(const BridgeRequest & request);

  // ---------------------------------------------------------------------------
  // Config Reload Helpers (Called by reload_and_update_bridges())
  // ---------------------------------------------------------------------------
  void remove_bridges_by_config(
    std::vector<ActiveBridgeR2A> & to_remove_r2a, std::vector<ActiveBridgeA2R> & to_remove_a2r);
  void calculate_new_bridges_to_add(std::vector<BridgeConfigEntry> & to_add);
  void launch_new_bridges(const std::vector<BridgeConfigEntry> & to_add);
  void launch_bridge_from_request(const BridgeConfigEntry & entry);
  void removed_bridges(
    const std::vector<ActiveBridgeR2A> & to_remove_r2a,
    const std::vector<ActiveBridgeA2R> & to_remove_a2r);

  // ---------------------------------------------------------------------------
  // General Check / Helper Functions
  // ---------------------------------------------------------------------------
  bool is_request_allowed(const BridgeRequest & req) const;
  bool is_topic_allowed(const std::string & topic_name, BridgeDirection direction) const;
  bool does_bridge_exist(const BridgeRequest & req) const;
  bool check_r2a_demand(const std::string & topic_name, pid_t self_pid) const;
  bool check_a2r_demand(const std::string & topic_name, pid_t self_pid) const;
  bool direction_matches(BridgeDirection entry, BridgeDirection required) const;

  bool has_external_ros2_publisher(const std::string & topic_name) const;
  bool has_external_ros2_subscriber(const std::string & topic_name) const;

  // ---------------------------------------------------------------------------
  // Template Functions
  // ---------------------------------------------------------------------------

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

    SubscriptionT subscription = create_bridge_ptr(
      this->node_, std::string(request.topic_name), rclcpp::QoS(DEFAULT_BRIDGE_QOS_DEPTH));

    RCLCPP_INFO(
      this->logger_, "Bridge created for topic: '%s' [Type: %s, Direction: %s]", request.topic_name,
      request.message_type, plugin_suffix.c_str());

    if (subscription) {
      auto topic_matches = [&](const auto & bridge) {
        return bridge.topic_name == std::string(request.topic_name);
      };
      if (std::any_of(active_bridges_vec.begin(), active_bridges_vec.end(), topic_matches)) {
        dlclose(handle);
        return;
      }
      active_bridges_vec.push_back({request.topic_name, subscription, handle});
    } else {
      dlclose(handle);
    }
  }

  template <typename Matcher>
  bool check_filter_rules(
    FilterMode mode, const std::vector<BridgeConfigEntry> & rules, Matcher matcher) const
  {
    switch (mode) {
      case FilterMode::ALLOW_ALL:
        return true;
      case FilterMode::WHITELIST:
        return std::any_of(rules.begin(), rules.end(), matcher);
      case FilterMode::BLACKLIST:
        return !std::any_of(rules.begin(), rules.end(), matcher);
    }
    return false;
  }

  template <typename IoctlArgs>
  bool has_agnocast_demand(
    const std::string & topic_name, pid_t self_pid, unsigned long ioctl_cmd,
    const char * entity_type_name, std::function<int(const IoctlArgs &)> get_count_func)
  {
    IoctlArgs args = {};
    args.topic_name = {topic_name.c_str(), topic_name.size()};
    args.exclude_pid = self_pid;

    if (ioctl(agnocast_fd, ioctl_cmd, &args) < 0) {
      RCLCPP_ERROR(
        logger_, "Failed to get external %s count for '%s'. Assuming demand exists.",
        entity_type_name, topic_name.c_str());
      return true;
    }

    return get_count_func(args) > 0;
  }

  bool has_ros2_demand(const std::string & topic_name, BridgeDirection direction)
  {
    if (this->bridge_config_.mode != FilterMode::ALLOW_ALL) {
      return true;
    }

    if (!this->node_) {
      return false;
    }

    try {
      if (direction == BridgeDirection::ROS2_TO_AGNOCAST) {
        return this->has_external_ros2_publisher(topic_name);
      } else if (direction == BridgeDirection::AGNOCAST_TO_ROS2) {
        return this->has_external_ros2_subscriber(topic_name);
      }
    } catch (const std::exception & e) {
      RCLCPP_ERROR(
        this->logger_, "Failed to check ROS 2 entity for topic '%s': %s. Assuming no demand.",
        topic_name.c_str(), e.what());
      return false;
    }

    return false;
  }

  template <typename BridgeType, typename IoctlArgs>
  void check_and_shutdown_collection(
    std::vector<BridgeType> & bridges, pid_t self_pid, unsigned long ioctl_cmd,
    BridgeDirection direction, const char * entity_type_name,
    std::function<int(const IoctlArgs &)> get_count_func)
  {
    std::set<void *> handles_to_remove;

    std::lock_guard<std::mutex> lock(this->bridges_mutex_);

    for (const auto & bridge : bridges) {
      bool agnocast_demand = this->has_agnocast_demand<IoctlArgs>(
        bridge.topic_name, self_pid, ioctl_cmd, entity_type_name, get_count_func);

      bool ros2_demand = this->has_ros2_demand(bridge.topic_name, direction);

      if (!agnocast_demand || !ros2_demand) {
        handles_to_remove.insert(bridge.plugin_handle);
      }
    }

    if (handles_to_remove.empty()) {
      return;
    }

    bridges.erase(
      std::remove_if(
        bridges.begin(), bridges.end(),
        [&](const BridgeType & bridge) {
          return handles_to_remove.count(bridge.plugin_handle) > 0;
        }),
      bridges.end());

    for (void * handle : handles_to_remove) {
      dlclose(handle);
    }
  }
};

}  // namespace agnocast

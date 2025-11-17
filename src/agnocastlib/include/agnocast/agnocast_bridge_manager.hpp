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
  // 1. Static Members (Signal Handling)
  // ---------------------------------------------------------------------------
  static std::atomic<bool> reload_filter_request_;
  static void sighup_handler(int signum);

  // ---------------------------------------------------------------------------
  // 2. Data Members (State Management)
  // ---------------------------------------------------------------------------
  std::vector<ActiveBridgeR2A> active_r2a_bridges_;
  std::vector<ActiveBridgeA2R> active_a2r_bridges_;
  std::vector<std::future<void>> worker_futures_;  // Futures for bridge worker threads
  mutable std::mutex bridges_mutex_;               // Protects active bridge vectors

  // ---------------------------------------------------------------------------
  // 3. Data Members (Core Components)
  // ---------------------------------------------------------------------------
  rclcpp::Node::SharedPtr node_;
  rclcpp::Logger logger_;
  BridgeConfig bridge_config_;  // Current filter configuration
  std::unique_ptr<rclcpp::Executor> executor_;
  std::thread spin_thread_;  // Thread for spinning the executor

  // ---------------------------------------------------------------------------
  // 4. Data Members (IPC / Event Monitoring)
  // ---------------------------------------------------------------------------
  mqd_t mq_;                 // POSIX Message Queue descriptor
  int epoll_fd_;             // epoll file descriptor
  std::string mq_name_str_;  // Message Queue name

  // ---------------------------------------------------------------------------
  // 5. Initialization / Setup (Called from constructor)
  // ---------------------------------------------------------------------------
  void setup_message_queue();
  void setup_signal_handler();
  void setup_epoll();
  std::unique_ptr<rclcpp::Executor> select_executor();
  BridgeConfig parse_bridge_config();
  void parse_rules_node(const YAML::Node & rules, BridgeConfig & config);

  // ---------------------------------------------------------------------------
  // 6. Main Loop Tasks (Called periodically from run())
  // ---------------------------------------------------------------------------
  void handle_bridge_request(const BridgeRequest & req);
  void reload_and_update_bridges();
  void discover_ros2_topics_for_allow_all();
  void check_and_remove_bridges();
  void check_and_request_rclcpp_shutdown();
  void cleanup_finished_futures();

  // ---------------------------------------------------------------------------
  // 7. Bridge Creation (Async thread entry points)
  // ---------------------------------------------------------------------------
  void launch_r2a_bridge_thread(const BridgeRequest & request);
  void launch_a2r_bridge_thread(const BridgeRequest & request);

  // ---------------------------------------------------------------------------
  // 8. Config Reload Helpers (Called by reload_and_update_bridges())
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
  // 9. General Check / Helper Functions
  // ---------------------------------------------------------------------------
  bool is_request_allowed(const BridgeRequest & req) const;
  bool is_topic_allowed(const std::string & topic_name, BridgeDirection direction) const;
  bool does_bridge_exist(const BridgeRequest & req) const;
  bool check_r2a_demand(const std::string & topic_name, pid_t self_pid) const;
  bool check_a2r_demand(const std::string & topic_name, pid_t self_pid) const;
  bool direction_matches(BridgeDirection entry, BridgeDirection required) const;

  // static std::atomic<bool> reload_filter_request_;

  // std::vector<ActiveBridgeR2A> active_r2a_bridges_;
  // std::vector<ActiveBridgeA2R> active_a2r_bridges_;
  // std::vector<std::future<void>> worker_futures_;

  // mutable std::mutex bridges_mutex_;

  // rclcpp::Node::SharedPtr node_;
  // rclcpp::Logger logger_;
  // BridgeConfig bridge_config_;
  // std::unique_ptr<rclcpp::Executor> executor_;
  // std::thread spin_thread_;

  // mqd_t mq_;
  // int epoll_fd_;
  // std::string mq_name_str_;

  // void setup_message_queue();
  // void setup_signal_handler();
  // void setup_epoll();
  // void cleanup_finished_futures();

  // void launch_r2a_bridge_thread(const BridgeRequest & request);
  // void launch_a2r_bridge_thread(const BridgeRequest & request);

  // bool direction_matches(BridgeDirection entry, BridgeDirection required) const;

  // bool is_request_allowed(const BridgeRequest & req) const;
  // bool is_topic_allowed(const std::string & topic_name, BridgeDirection direction) const;
  // bool does_bridge_exist(const BridgeRequest & req) const;
  // void handle_bridge_request(const BridgeRequest & req);

  // void remove_bridges_by_config(
  //   std::vector<ActiveBridgeR2A> & to_remove_r2a, std::vector<ActiveBridgeA2R> & to_remove_a2r);
  // void calculate_new_bridges_to_add(std::vector<BridgeConfigEntry> & to_add);

  // bool check_r2a_demand(const std::string & topic_name, pid_t self_pid) const;
  // bool check_a2r_demand(const std::string & topic_name, pid_t self_pid) const;
  // void launch_bridge_from_request(const BridgeConfigEntry & entry);
  // void removed_bridges(
  //   const std::vector<ActiveBridgeR2A> & to_remove_r2a,
  //   const std::vector<ActiveBridgeA2R> & to_remove_a2r);
  // void launch_new_bridges(const std::vector<BridgeConfigEntry> & to_add);
  // void reload_and_update_bridges();

  // void discover_ros2_topics_for_allow_all();
  // void check_and_remove_bridges();
  // void check_and_request_rclcpp_shutdown();

  // BridgeConfig parse_bridge_config();
  // void parse_rules_node(const YAML::Node & rules, BridgeConfig & config);
  // std::unique_ptr<rclcpp::Executor> select_executor();

  // static void sighup_handler(int signum);

  // ---------------------------------------------------------------------------
  // 10. Template Functions
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

    if (subscription) {
      std::lock_guard<std::mutex> lock(this->bridges_mutex_);
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

  template <typename BridgeType, typename IoctlArgs>
  void check_and_shutdown_collection(
    std::vector<BridgeType> & bridges, pid_t self_pid, unsigned long ioctl_cmd,
    BridgeDirection direction, const char * entity_type_name,
    std::function<int(const IoctlArgs &)> get_count_func)
  {
    std::vector<void *> handles_to_close;
    {
      std::lock_guard<std::mutex> lock(this->bridges_mutex_);
      bridges.erase(
        std::remove_if(
          bridges.begin(), bridges.end(),
          [&](const BridgeType & bridge) {
            IoctlArgs args = {};
            args.topic_name = {bridge.topic_name.c_str(), bridge.topic_name.size()};
            args.exclude_pid = self_pid;
            bool agnocast_demand = true;

            if (ioctl(agnocast_fd, ioctl_cmd, &args) < 0) {
              RCLCPP_ERROR(
                logger_, "Failed to get external %s count for '%s'", entity_type_name,
                bridge.topic_name.c_str());
              return false;
            }

            if (get_count_func(args) == 0) {
              agnocast_demand = false;
            }

            bool ros2_demand = true;
            if (this->bridge_config_.mode == FilterMode::ALLOW_ALL) {
              if (!this->node_) {
                ros2_demand = false;
              } else {
                const std::string topic_name_str(bridge.topic_name);
                try {
                  if (direction == BridgeDirection::ROS2_TO_AGNOCAST) {
                    auto publishers_info =
                      this->node_->get_publishers_info_by_topic(topic_name_str);
                    ros2_demand = !publishers_info.empty();
                  } else if (direction == BridgeDirection::AGNOCAST_TO_ROS2) {
                    auto subscriptions_info =
                      this->node_->get_subscriptions_info_by_topic(topic_name_str);
                    ros2_demand = !subscriptions_info.empty();
                  } else {
                    ros2_demand = false;
                  }
                } catch (const std::exception & e) {
                  RCLCPP_ERROR(
                    this->logger_, "Failed to check ROS 2 entity for topic '%s': %s",
                    topic_name_str.c_str(), e.what());
                  ros2_demand = false;
                }
              }
            }

            if (!agnocast_demand && !ros2_demand) {
              handles_to_close.push_back(bridge.plugin_handle);
              return true;
            }

            return false;
          }),
        bridges.end());
    }

    for (void * handle : handles_to_close) {
      dlclose(handle);
    }
  }
};

}  // namespace agnocast

#pragma once

#include "agnocast/agnocast_bridge_node_r2a.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <mqueue.h>

#include <atomic>
#include <functional>
#include <mutex>
#include <string>
#include <vector>

constexpr pid_t NO_OPPOSITE_BRIDGE_PID = -1;

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
  static std::atomic<bool> running_;

  struct ActiveBridge
  {
    pid_t pid;
    std::string topic_name;
  };

  std::vector<ActiveBridge> active_r2a_bridges_;
  std::vector<ActiveBridge> active_a2r_bridges_;

  mutable std::mutex bridges_mutex_;

  mqd_t mq_;
  int epoll_fd_;
  std::string mq_name_str_;

  void setup_message_queue();
  void setup_epoll();
  void setup_signal_handlers();

  static void sigchld_handler(int sig);
  static void shutdown_handler(int sig);

  std::vector<ActiveBridge> & get_bridge_list(BridgeDirection direction);

  bool does_bridge_exist(BridgeDirection direction, const std::string & topic_name);
  void handle_bridge_request(const MqMsgBridge & req);

  void remove_bridges(
    std::vector<ActiveBridge> & bridges, std::function<bool(const std::string &)> check_demand);

  bool check_r2a_demand(const std::string & topic_name) const;
  bool check_a2r_demand(const std::string & topic_name) const;

  void check_and_remove_bridges();
  void check_and_request_shutdown();

  template <typename IoctlArgs>
  bool check_demand_internal(
    const std::string & topic_name, const std::vector<ActiveBridge> & opposite_bridges,
    unsigned long ioctl_cmd, std::function<int(const IoctlArgs &)> get_result) const
  {
    pid_t opposite_pid = NO_OPPOSITE_BRIDGE_PID;
    auto it = std::find_if(
      opposite_bridges.begin(), opposite_bridges.end(),
      [&](const ActiveBridge & bridge) { return bridge.topic_name == topic_name; });

    if (it != opposite_bridges.end()) {
      opposite_pid = it->pid;
    }

    IoctlArgs args = {};
    args.topic_name = {topic_name.c_str(), topic_name.size()};
    args.exclude_pid = opposite_pid;

    if (ioctl(agnocast_fd, ioctl_cmd, &args) < 0) {
      RCLCPP_ERROR(logger, "Failed for '%s'", topic_name.c_str());
      return false;
    }

    return get_result(args) > 0;
  }
};

}  // namespace agnocast

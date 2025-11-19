#pragma once

#include "agnocast/agnocast_bridge_node.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

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

  std::vector<ActiveBridge> active_bridges_;

  mutable std::mutex bridges_mutex_;

  mqd_t mq_;
  int epoll_fd_;
  std::string mq_name_str_;

  void setup_message_queue();
  void setup_epoll();
  void setup_signal_handlers();

  static void sigchld_handler(int sig);
  static void shutdown_handler(int sig);

  bool does_bridge_exist(const std::string & topic_name);
  void handle_bridge_request(const MqMsgBridge & req);

  void remove_bridges(
    std::vector<ActiveBridge> & bridges,
    std::function<bool(const std::string &, pid_t)> check_demand_r2a,
    std::function<bool(const std::string &, pid_t)> check_demand_a2r);

  bool check_r2a_demand(const std::string & topic_name, pid_t bridge_pid) const;
  bool check_a2r_demand(const std::string & topic_name, pid_t bridge_pid) const;

  void check_and_remove_bridges();
  void check_and_request_shutdown();

  template <typename IoctlArgs>
  bool check_demand_internal(
    const std::string & topic_name, pid_t bridge_pid, unsigned long ioctl_cmd,
    std::function<int(const IoctlArgs &)> get_result) const
  {
    IoctlArgs args = {};
    args.topic_name = {topic_name.c_str(), topic_name.size()};
    args.exclude_pid = bridge_pid;

    if (ioctl(agnocast_fd, ioctl_cmd, &args) < 0) {
      RCLCPP_ERROR(logger, "Failed for '%s'", topic_name.c_str());
      return false;
    }

    return get_result(args) > 0;
  }
};

}  // namespace agnocast

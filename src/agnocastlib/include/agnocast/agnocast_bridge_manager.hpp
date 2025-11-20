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
    MqMsgBridge req;
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
  pid_t spawn_bridge_process(const MqMsgBridge & req);
  void handle_bridge_request(const MqMsgBridge & req);

  bool is_bridge_needed(const std::string & topic_name, pid_t bridge_pid) const;

  void maintain_bridges();
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

#pragma once

#include "agnocast/agnocast_bridge_node.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <ament_index_cpp/get_package_prefix.hpp>
#include <rclcpp/rclcpp.hpp>

#include <dlfcn.h>
#include <mqueue.h>
#include <sys/ioctl.h>

#include <algorithm>
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
  static void sigchld_handler(int sig);

  bool does_bridge_exist(const MqMsgBridge & req) const;
  void handle_bridge_request(const MqMsgBridge & req);

  bool check_r2a_demand(const std::string & topic_name) const;
  bool check_a2r_demand(const std::string & topic_name) const;

  void check_and_remove_bridges();
  void check_and_request_shutdown();
};

}  // namespace agnocast

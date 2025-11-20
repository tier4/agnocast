#pragma once

#include "agnocast/agnocast_mq.hpp"

#include <mqueue.h>
#include <sys/types.h>

#include <map>
#include <string>

namespace agnocast
{

extern int agnocast_fd;

class BridgeGenerator
{
public:
  explicit BridgeGenerator(pid_t target_pid);
  ~BridgeGenerator();

  BridgeGenerator(const BridgeGenerator &) = delete;
  BridgeGenerator & operator=(const BridgeGenerator &) = delete;
  BridgeGenerator(BridgeGenerator &&) = delete;
  BridgeGenerator & operator=(BridgeGenerator &&) = delete;

  void run();

private:
  void setup_mq();
  void setup_signals();
  void setup_epoll();

  void handle_mq_event();
  void handle_signal_event();
  void generate_bridge(const MqMsgBridge & req);
  void check_watched_bridges();
  pid_t get_running_bridge_pid(const std::string & topic_name);
  void reap_zombies();

  const pid_t target_pid_;
  std::string mq_name_;

  mqd_t mq_fd_ = (mqd_t)-1;
  int epoll_fd_ = -1;
  int signal_fd_ = -1;

  struct WatchedBridge
  {
    pid_t pid;
    MqMsgBridge req;
  };

  bool shutdown_requested_ = false;
  std::map<pid_t, MqMsgBridge> local_managed_bridges_;
  std::map<std::string, WatchedBridge> watched_bridges_;
};

}  // namespace agnocast
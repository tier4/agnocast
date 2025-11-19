#pragma once

#include <mqueue.h>
#include <sys/types.h>

#include <string>

namespace agnocast
{

struct MqMsgBridge;

class BridgeGenerator
{
public:
  explicit BridgeGenerator(pid_t target_pid);

  ~BridgeGenerator();

  BridgeGenerator(const BridgeGenerator &) = delete;
  BridgeGenerator & operator=(const BridgeGenerator &) = delete;

  void run();

private:
  pid_t target_pid_;
  std::string mq_name_;

  mqd_t mq_fd_;
  int epoll_fd_;
  int signal_fd_;

  bool shutdown_requested_;

  void setup_mq();
  void setup_signals();
  void setup_epoll();

  void handle_mq_event();
  void handle_signal_event();
  void spawn_bridge(const MqMsgBridge & req);
  void reap_zombies();
};

}  // namespace agnocast
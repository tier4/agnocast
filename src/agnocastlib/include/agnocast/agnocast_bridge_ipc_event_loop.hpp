#pragma once

#include <rclcpp/logger.hpp>

#include <mqueue.h>
#include <sys/types.h>

#include <string>

namespace agnocast
{

class BridgeIpcEventLoop
{
public:
  BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger & logger);
  ~BridgeIpcEventLoop();

  BridgeIpcEventLoop(const BridgeIpcEventLoop &) = delete;
  BridgeIpcEventLoop & operator=(const BridgeIpcEventLoop &) = delete;

  bool spin_once(int timeout_ms);

private:
  rclcpp::Logger logger_;

  int epoll_fd_ = -1;

  void setup_epoll();

  mqd_t mq_parent_fd_ = (mqd_t)-1;
  mqd_t mq_child_fd_ = (mqd_t)-1;

  std::string mq_parent_name_;
  std::string mq_child_name_;

  void setup_mq(pid_t target_pid);
  // TODO:: signal, epoll setup will be implemented in following PRs

  void cleanup_resources();
};

}  // namespace agnocast

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

  mqd_t mq_parent_fd_ = (mqd_t)-1;

  std::string mq_parent_name_;

  void setup_mq(pid_t target_pid);
  void setup_epoll();

  mqd_t create_and_open_mq(const std::string & name, const std::string & label);
  void add_fd_to_epoll(int fd, const std::string & label);

  void cleanup_resources();
};

}  // namespace agnocast

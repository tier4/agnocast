#pragma once

#include "rclcpp/rclcpp.hpp"

#include <mqueue.h>
#include <sys/epoll.h>
#include <sys/types.h>

#include <functional>
#include <string>

namespace agnocast
{

class BridgeIpcEventLoop
{
public:
  using EventCallback = std::function<void(int fd)>;
  using SignalCallback = std::function<void()>;

  BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger & logger);
  ~BridgeIpcEventLoop();

  BridgeIpcEventLoop(const BridgeIpcEventLoop &) = delete;
  BridgeIpcEventLoop & operator=(const BridgeIpcEventLoop &) = delete;

  void set_parent_mq_handler(EventCallback cb);
  void set_child_mq_handler(EventCallback cb);
  void set_signal_handler(SignalCallback cb);

  bool spin_once(int timeout_ms);

  void close_parent_mq();

  mqd_t get_parent_mq_fd() const { return mq_parent_fd_; }
  mqd_t get_child_mq_fd() const { return mq_child_fd_; }

private:
  void setup_mq(pid_t target_pid);
  void setup_signals();
  void setup_epoll();

  rclcpp::Logger logger_;

  int epoll_fd_ = -1;
  int signal_fd_ = -1;
  mqd_t mq_parent_fd_ = (mqd_t)-1;
  mqd_t mq_child_fd_ = (mqd_t)-1;

  std::string mq_parent_name_;
  std::string mq_child_name_;

  EventCallback parent_cb_;
  EventCallback child_cb_;
  SignalCallback signal_cb_;
};

}  // namespace agnocast

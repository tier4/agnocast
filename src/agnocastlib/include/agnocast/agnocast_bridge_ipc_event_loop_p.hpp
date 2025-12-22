#pragma once

#include <rclcpp/logger.hpp>

#include <mqueue.h>

#include <csignal>
#include <functional>
#include <initializer_list>
#include <string>
#include <vector>

namespace agnocast
{

class BridgeIpcEventLoopP
{
public:
  using EventCallback = std::function<void(int)>;
  using SignalCallback = std::function<void()>;
  using ReloadCallback = std::function<void()>;

  explicit BridgeIpcEventLoopP(const rclcpp::Logger & logger);
  ~BridgeIpcEventLoopP();

  bool spin_once(int timeout_ms);

  void set_peer_mq_handler(EventCallback cb);
  void set_signal_handler(SignalCallback cb);
  void set_reload_handler(ReloadCallback cb);

private:
  void setup_mq();
  void setup_signals();
  void setup_epoll();
  void cleanup_resources();

  void ignore_signals(std::initializer_list<int> signals);
  sigset_t block_signals(std::initializer_list<int> signals);

  mqd_t create_and_open_mq(const std::string & name, const std::string & label);
  void add_fd_to_epoll(int fd, const std::string & label) const;

  rclcpp::Logger logger_;

  int epoll_fd_ = -1;
  int signal_fd_ = -1;
  int reload_fd_ = -1;

  mqd_t mq_peer_fd_ = -1;
  std::string mq_self_name_;

  EventCallback peer_cb_;
  SignalCallback signal_cb_;
  ReloadCallback reload_cb_;
};

}  // namespace agnocast

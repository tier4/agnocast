#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"

#include <rclcpp/logging.hpp>

#include <sys/epoll.h>
#include <unistd.h>

#include <array>
#include <cerrno>
#include <cstring>
#include <stdexcept>
#include <string>

namespace agnocast
{

BridgeIpcEventLoop::BridgeIpcEventLoop(pid_t /*target_pid*/, const rclcpp::Logger & logger)
: logger_(logger)
{
  try {
    setup_epoll();
  } catch (...) {
    if (epoll_fd_ != -1) {
      close(epoll_fd_);
    }
    throw;
  }
}

BridgeIpcEventLoop::~BridgeIpcEventLoop()
{
  if (epoll_fd_ != -1) {
    close(epoll_fd_);
    epoll_fd_ = -1;
  }
}

bool BridgeIpcEventLoop::spin_once(int timeout_ms)
{
  constexpr int MAX_EVENTS = 10;
  std::array<struct epoll_event, MAX_EVENTS> events{};

  int n = -1;
  do {
    n = epoll_wait(epoll_fd_, events.data(), MAX_EVENTS, timeout_ms);
  } while (n < 0 && errno == EINTR);

  if (n < 0) {
    RCLCPP_ERROR(logger_, "epoll_wait failed: %s", strerror(errno));
    return false;
  }

  if (n == 0) {
    return false;
  }

  for (int i = 0; i < n; ++i) {
    // TODO(yutarokobayashi): Event  processing (mq, signal)
  }

  return true;
}

void BridgeIpcEventLoop::setup_epoll()
{
  epoll_fd_ = epoll_create1(EPOLL_CLOEXEC);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed: " + std::string(strerror(errno)));
  }

  // TODO(yutarokobayashi): Add epoll (mq, signal)
}

}  // namespace agnocast

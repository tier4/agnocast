#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <rclcpp/logging.hpp>

#include <fcntl.h>
#include <sys/epoll.h>
#include <sys/stat.h>
#include <unistd.h>

#include <array>
#include <cerrno>
#include <cstring>
#include <stdexcept>
#include <string>
#include <system_error>

namespace agnocast
{

constexpr int64_t MQ_MAX_MESSAGES = 10;
constexpr int64_t MQ_MESSAGE_SIZE = sizeof(MqMsgBridge);
constexpr mode_t MQ_PERMS = 0600;

BridgeIpcEventLoop::BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger & logger)
: logger_(logger)
{
  try {
    setup_mq(target_pid);
    setup_epoll();
  } catch (...) {
    cleanup_resources();
    throw;
  }
}

BridgeIpcEventLoop::~BridgeIpcEventLoop()
{
  cleanup_resources();
}

bool BridgeIpcEventLoop::spin_once(int timeout_ms)
{
  constexpr int MAX_EVENTS = 10;
  std::array<struct epoll_event, MAX_EVENTS> events{};

  int event_count = -1;
  do {
    event_count = epoll_wait(epoll_fd_, events.data(), MAX_EVENTS, timeout_ms);
  } while (event_count < 0 && errno == EINTR);
  if (event_count < 0) {
    RCLCPP_ERROR(logger_, "epoll_wait failed: %s", strerror(errno));
    return false;
  }
  if (event_count == 0) {
    return true;
  }
  for (int event_index = 0; event_index < event_count; ++event_index) {
    int fd = events[event_index].data.fd;
    if (fd == mq_parent_fd_) {  // NOLINT(bugprone-branch-clone)
      // TODO(yutarokobayashi): run event_loop parent handler.
    } else {
      // TODO(yutarokobayashi): run event_loop other handler.
    }
  }

  return true;
}

void BridgeIpcEventLoop::setup_mq(pid_t target_pid)
{
  mq_parent_name_ = create_mq_name_for_bridge_parent(target_pid);
  mq_parent_fd_ = create_and_open_mq(mq_parent_name_, "Parent");
}

void BridgeIpcEventLoop::setup_epoll()
{
  epoll_fd_ = epoll_create1(EPOLL_CLOEXEC);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed: " + std::string(strerror(errno)));
  }

  add_fd_to_epoll(mq_parent_fd_, "Parent MQ");
}

mqd_t BridgeIpcEventLoop::create_and_open_mq(const std::string & name, const std::string & label)
{
  struct mq_attr attr = {};
  attr.mq_maxmsg = MQ_MAX_MESSAGES;
  attr.mq_msgsize = MQ_MESSAGE_SIZE;

  // Cleanup any stale queue from previous runs before creating a new one.
  if (mq_unlink(name.c_str()) == -1) {
    if (errno != ENOENT) {
      RCLCPP_WARN(logger_, "mq_unlink failed for %s: %s", name.c_str(), strerror(errno));
      throw std::system_error(errno, std::generic_category(), label + " MQ unlink failed");
    }
  }

  mqd_t fd = mq_open(name.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK | O_CLOEXEC, MQ_PERMS, &attr);

  if (fd == -1) {
    throw std::system_error(errno, std::generic_category(), label + " MQ open failed");
  }

  return fd;
}

void BridgeIpcEventLoop::add_fd_to_epoll(int fd, const std::string & label) const
{
  struct epoll_event ev = {};
  ev.events = EPOLLIN;
  ev.data.fd = fd;

  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, fd, &ev) == -1) {
    throw std::runtime_error("epoll_ctl (" + label + ") failed: " + std::string(strerror(errno)));
  }
}

void BridgeIpcEventLoop::cleanup_resources()
{
  if (epoll_fd_ != -1) {
    if (close(epoll_fd_) == -1) {
      RCLCPP_WARN(logger_, "Failed to close epoll_fd: %s", strerror(errno));
    }
    epoll_fd_ = -1;
  }

  if (mq_parent_fd_ != -1) {
    if (mq_close(mq_parent_fd_) == -1) {
      RCLCPP_WARN(logger_, "Failed to close mq_parent_fd: %s", strerror(errno));
    }
    mq_parent_fd_ = -1;
  }

  if (!mq_parent_name_.empty()) {
    if (mq_unlink(mq_parent_name_.c_str()) == -1) {
      if (errno != ENOENT) {
        RCLCPP_WARN(
          logger_, "Failed to unlink mq %s: %s", mq_parent_name_.c_str(), strerror(errno));
      }
    }
    mq_parent_name_.clear();
  }
}

}  // namespace agnocast

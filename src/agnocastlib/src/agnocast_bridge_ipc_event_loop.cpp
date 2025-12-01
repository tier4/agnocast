#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <fcntl.h>
#include <sys/prctl.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstring>
#include <stdexcept>

namespace agnocast
{

BridgeIpcEventLoop::BridgeIpcEventLoop(pid_t target_pid, rclcpp::Logger logger) : logger_(logger)
{
  setup_mq(target_pid);
  setup_signals();
  setup_epoll();
}

BridgeIpcEventLoop::~BridgeIpcEventLoop()
{
  auto close_fd = [](int & fd) {
    if (fd != -1) {
      close(fd);
      fd = -1;
    }
  };

  auto close_and_unlink_mq = [](mqd_t & fd, const std::string & name) {
    if (fd != (mqd_t)-1) {
      mq_close(fd);
      fd = (mqd_t)-1;
    }
    if (!name.empty()) {
      mq_unlink(name.c_str());
    }
  };

  close_and_unlink_mq(mq_parent_fd_, mq_parent_name_);
  close_and_unlink_mq(mq_child_fd_, mq_child_name_);
  close_fd(epoll_fd_);
  close_fd(signal_fd_);
}

void BridgeIpcEventLoop::set_parent_mq_handler(EventCallback cb)
{
  parent_cb_ = cb;
}
void BridgeIpcEventLoop::set_child_mq_handler(EventCallback cb)
{
  child_cb_ = cb;
}
void BridgeIpcEventLoop::set_signal_handler(SignalCallback cb)
{
  signal_cb_ = cb;
}

bool BridgeIpcEventLoop::spin_once(int timeout_ms)
{
  constexpr int MAX_EVENTS = 10;
  struct epoll_event events[MAX_EVENTS];

  int n = epoll_wait(epoll_fd_, events, MAX_EVENTS, timeout_ms);

  if (n < 0) {
    if (errno != EINTR) {
      RCLCPP_ERROR(logger_, "epoll_wait failed: %s", strerror(errno));
    }
    return false;
  }

  if (n == 0) {
    return false;
  }

  for (int i = 0; i < n; ++i) {
    int fd = events[i].data.fd;

    if (fd == mq_parent_fd_) {
      if (parent_cb_) parent_cb_(fd);
    } else if (fd == mq_child_fd_) {
      if (child_cb_) child_cb_(fd);
    } else if (fd == signal_fd_) {
      struct signalfd_siginfo fdsi;
      ssize_t s = read(signal_fd_, &fdsi, sizeof(struct signalfd_siginfo));
      if (s == sizeof(struct signalfd_siginfo)) {
        if ((fdsi.ssi_signo == SIGTERM || fdsi.ssi_signo == SIGINT) && signal_cb_) {
          signal_cb_();
        }
      }
    }
  }

  return true;
}

void BridgeIpcEventLoop::close_parent_mq()
{
  if (mq_parent_fd_ != (mqd_t)-1) {
    epoll_ctl(epoll_fd_, EPOLL_CTL_DEL, mq_parent_fd_, nullptr);

    mq_close(mq_parent_fd_);
    mq_unlink(mq_parent_name_.c_str());

    mq_parent_fd_ = (mqd_t)-1;
  }
}

void BridgeIpcEventLoop::setup_mq(pid_t target_pid)
{
  auto create_and_open = [](const std::string & name, const std::string & label) -> mqd_t {
    struct mq_attr attr{};
    attr.mq_maxmsg = 10;
    attr.mq_msgsize = sizeof(MqMsgBridge);

    mq_unlink(name.c_str());

    mqd_t fd = mq_open(name.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK | O_CLOEXEC, 0600, &attr);

    if (fd == (mqd_t)-1) {
      throw std::runtime_error(label + " MQ open failed: " + std::string(strerror(errno)));
    }
    return fd;
  };

  mq_parent_name_ = create_mq_name_for_bridge_parent(target_pid);
  mq_parent_fd_ = create_and_open(mq_parent_name_, "Parent");

  mq_child_name_ = create_mq_name_for_bridge_child(getpid());
  mq_child_fd_ = create_and_open(mq_child_name_, "Child");
}

void BridgeIpcEventLoop::setup_signals()
{
  for (int sig : {SIGPIPE, SIGHUP}) {
    ::signal(sig, SIG_IGN);
  }

  sigset_t mask;
  sigemptyset(&mask);
  for (int sig : {SIGTERM, SIGINT}) {
    sigaddset(&mask, sig);
  }

  if (sigprocmask(SIG_BLOCK, &mask, nullptr) == -1) {
    throw std::runtime_error("sigprocmask failed: " + std::string(strerror(errno)));
  }

  signal_fd_ = signalfd(-1, &mask, SFD_NONBLOCK | SFD_CLOEXEC);
  if (signal_fd_ == -1) {
    throw std::runtime_error("signalfd failed: " + std::string(strerror(errno)));
  }
}

void BridgeIpcEventLoop::setup_epoll()
{
  epoll_fd_ = epoll_create1(EPOLL_CLOEXEC);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed: " + std::string(strerror(errno)));
  }

  auto add_to_epoll = [this](int fd, const std::string & label) {
    struct ::epoll_event ev{};
    ev.events = EPOLLIN;
    ev.data.fd = fd;

    if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, fd, &ev) == -1) {
      throw std::runtime_error("epoll_ctl (" + label + ") failed: " + std::string(strerror(errno)));
    }
  };

  add_to_epoll(mq_parent_fd_, "Parent MQ");
  add_to_epoll(mq_child_fd_, "Child MQ");
  add_to_epoll(signal_fd_, "Signal");
}

}  // namespace agnocast

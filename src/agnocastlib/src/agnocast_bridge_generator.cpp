#include "agnocast/agnocast_bridge_generator.hpp"

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <fcntl.h>
#include <signal.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cstring>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace agnocast
{

extern int agnocast_fd;

BridgeGenerator::BridgeGenerator(pid_t target_pid)
: target_pid_(target_pid),
  mq_fd_((mqd_t)-1),
  epoll_fd_(-1),
  signal_fd_(-1),
  shutdown_requested_(false)
{
  if (prctl(PR_SET_PDEATHSIG, SIGTERM) == -1) {
    throw std::runtime_error("prctl failed");
  }

  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  setup_mq();
  setup_signals();
  setup_epoll();
}

BridgeGenerator::~BridgeGenerator()
{
  if (epoll_fd_ != -1) close(epoll_fd_);
  if (signal_fd_ != -1) close(signal_fd_);
  if (mq_fd_ != (mqd_t)-1) mq_close(mq_fd_);

  if (!mq_name_.empty()) {
    mq_unlink(mq_name_.c_str());
  }
}

void BridgeGenerator::setup_mq()
{
  mq_name_ = create_mq_name_for_bridge(target_pid_);
  mq_unlink(mq_name_.c_str());

  struct mq_attr attr{};
  attr.mq_maxmsg = 10;
  attr.mq_msgsize = sizeof(MqMsgBridge);

  mq_fd_ = mq_open(mq_name_.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK, 0644, &attr);
  if (mq_fd_ == (mqd_t)-1) {
    throw std::runtime_error("MQ open failed: " + std::string(strerror(errno)));
  }
}

void BridgeGenerator::setup_signals()
{
  sigset_t mask;
  sigemptyset(&mask);
  sigaddset(&mask, SIGTERM);
  sigaddset(&mask, SIGINT);

  if (sigprocmask(SIG_BLOCK, &mask, nullptr) == -1) {
    throw std::runtime_error("sigprocmask failed");
  }

  signal_fd_ = signalfd(-1, &mask, SFD_NONBLOCK | SFD_CLOEXEC);
  if (signal_fd_ == -1) {
    throw std::runtime_error("signalfd failed");
  }
}

void BridgeGenerator::setup_epoll()
{
  epoll_fd_ = epoll_create1(EPOLL_CLOEXEC);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed");
  }

  struct epoll_event ev{};

  ev.events = EPOLLIN;
  ev.data.fd = mq_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_fd_, &ev) == -1) {
    throw std::runtime_error("epoll_ctl (MQ) failed");
  }

  ev.events = EPOLLIN;
  ev.data.fd = signal_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, signal_fd_, &ev) == -1) {
    throw std::runtime_error("epoll_ctl (Signal) failed");
  }
}

void BridgeGenerator::run()
{
  constexpr int MAX_EVENTS = 10;
  struct epoll_event events[MAX_EVENTS];

  while (!shutdown_requested_) {
    if (kill(target_pid_, 0) != 0) break;

    reap_zombies();

    int n = epoll_wait(epoll_fd_, events, MAX_EVENTS, 1000);

    if (n < 0) {
      if (errno == EINTR) continue;
      break;  // Error
    }

    for (int i = 0; i < n; ++i) {
      int fd = events[i].data.fd;

      if (fd == mq_fd_) {
        handle_mq_event();
      } else if (fd == signal_fd_) {
        handle_signal_event();
      }
    }
  }
}

void BridgeGenerator::handle_mq_event()
{
  MqMsgBridge req;
  // Non-blocking read
  while (mq_receive(mq_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
    spawn_bridge(req);
  }
}

void BridgeGenerator::handle_signal_event()
{
  struct signalfd_siginfo fdsi;
  ssize_t s = read(signal_fd_, &fdsi, sizeof(struct signalfd_siginfo));

  if (s != sizeof(struct signalfd_siginfo)) return;

  if (fdsi.ssi_signo == SIGTERM || fdsi.ssi_signo == SIGINT) {
    shutdown_requested_ = true;
  }
}

void BridgeGenerator::spawn_bridge(const MqMsgBridge & req)
{
  pid_t b_pid = fork();

  if (b_pid < 0) return;

  if (b_pid == 0) {
    sigset_t mask;
    sigemptyset(&mask);
    sigprocmask(SIG_SETMASK, &mask, nullptr);

    if (setsid() == -1) {
      RCLCPP_ERROR(logger, "setsid failed for unlink daemon: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    struct ioctl_bridge_args bridge_args;
    std::memset(&bridge_args, 0, sizeof(bridge_args));
    safe_strncpy(bridge_args.info.topic_name, req.args.topic_name, MAX_TOPIC_NAME_LEN);
    bridge_args.info.pid = getpid();

    if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &bridge_args) < 0) {
      if (errno == EEXIST) {
        exit(0);
      }
      exit(EXIT_FAILURE);
    }

    extern void bridge_main(const MqMsgBridge &);
    bridge_main(req);

    ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &bridge_args);
    exit(0);
  }
}

void BridgeGenerator::reap_zombies()
{
  while (waitpid(-1, nullptr, WNOHANG) > 0);
}

}  // namespace agnocast
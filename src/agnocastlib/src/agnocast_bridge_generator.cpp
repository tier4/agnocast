#include "agnocast/agnocast_bridge_generator.hpp"

#include "agnocast/agnocast_bridge_main.hpp"
#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"
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
constexpr int EXIT_BRIDGE_ALREADY_EXISTS = 100;

BridgeGenerator::BridgeGenerator(pid_t target_pid) : target_pid_(target_pid)
{
  if (prctl(PR_SET_PDEATHSIG, SIGTERM) == -1) {
    throw std::runtime_error("prctl failed: " + std::string(strerror(errno)));
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
    throw std::runtime_error("sigprocmask failed: " + std::string(strerror(errno)));
  }

  signal_fd_ = signalfd(-1, &mask, SFD_NONBLOCK | SFD_CLOEXEC);
  if (signal_fd_ == -1) {
    throw std::runtime_error("signalfd failed: " + std::string(strerror(errno)));
  }
}

void BridgeGenerator::setup_epoll()
{
  epoll_fd_ = epoll_create1(EPOLL_CLOEXEC);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed: " + std::string(strerror(errno)));
  }

  struct epoll_event ev_mq{};
  ev_mq.events = EPOLLIN;
  ev_mq.data.fd = mq_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_fd_, &ev_mq) == -1) {
    throw std::runtime_error("epoll_ctl (MQ) failed");
  }

  struct epoll_event ev_sig{};
  ev_sig.events = EPOLLIN;
  ev_sig.data.fd = signal_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, signal_fd_, &ev_sig) == -1) {
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
    check_watched_bridges();

    int n = epoll_wait(epoll_fd_, events, MAX_EVENTS, 1000);

    if (n < 0) {
      if (errno == EINTR) continue;
      break;
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
  while (mq_receive(mq_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
    generate_bridge(req);
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

void BridgeGenerator::generate_bridge(const MqMsgBridge & req)
{
  pid_t b_pid = fork();

  if (b_pid < 0) {
    std::cerr << "[BridgeGenerator] fork failed: " << strerror(errno) << std::endl;
    return;
  }

  if (b_pid == 0) {
    sigset_t mask;
    sigemptyset(&mask);
    sigprocmask(SIG_SETMASK, &mask, nullptr);

    if (setsid() == -1) {
      std::cerr << "[BridgeGenerator] setsid failed: " << strerror(errno) << std::endl;
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    struct ioctl_bridge_args bridge_args{};
    safe_strncpy(bridge_args.info.topic_name, req.args.topic_name, MAX_TOPIC_NAME_LEN);
    bridge_args.info.pid = getpid();

    if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &bridge_args) < 0) {
      if (errno == EEXIST) {
        exit(EXIT_BRIDGE_ALREADY_EXISTS);
      }
      std::cerr << "[BridgeGenerator] Register failed: " << strerror(errno) << std::endl;
      exit(EXIT_FAILURE);
    }

    try {
      bridge_main(req);
    } catch (const std::exception & e) {
      std::cerr << "[BridgeGenerator] Exception in bridge_main: " << e.what() << std::endl;
    } catch (...) {
      std::cerr << "[BridgeGenerator] Unknown exception in bridge_main" << std::endl;
    }
    unregister_bridge(bridge_args.info.pid, bridge_args.info.topic_name);

    exit(0);
  } else {
    local_managed_bridges_[b_pid] = req;
  }
}

void BridgeGenerator::check_watched_bridges()
{
  for (auto it = watched_bridges_.begin(); it != watched_bridges_.end();) {
    pid_t target_pid = it->second.pid;
    const std::string & topic_name = it->first;
    MqMsgBridge req = it->second.req;

    if (kill(target_pid, 0) == -1 && errno == ESRCH) {
      bool r2a = check_r2a_demand(topic_name.c_str(), -1);
      bool a2r = check_a2r_demand(topic_name.c_str(), -1);

      if (r2a || a2r) {
        it = watched_bridges_.erase(it);
        generate_bridge(req);
      } else {
        it = watched_bridges_.erase(it);
      }
    } else {
      ++it;
    }
  }
}

pid_t BridgeGenerator::get_running_bridge_pid(const std::string & topic_name)
{
  struct ioctl_bridge_args args{};
  safe_strncpy(args.info.topic_name, topic_name.c_str(), MAX_TOPIC_NAME_LEN);
  args.info.pid = -1;

  if (ioctl(agnocast_fd, AGNOCAST_GET_BRIDGE_PID_CMD, &args) == 0) {
    return args.info.pid;
  }
  return -1;
}

void BridgeGenerator::reap_zombies()
{
  int status;
  pid_t pid;

  while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
    auto it = local_managed_bridges_.find(pid);
    if (it != local_managed_bridges_.end()) {
      MqMsgBridge req = it->second;
      local_managed_bridges_.erase(it);

      bool should_restart = false;

      if (WIFEXITED(status)) {
        int exit_code = WEXITSTATUS(status);

        if (exit_code == EXIT_BRIDGE_ALREADY_EXISTS) {
          pid_t winner_pid = get_running_bridge_pid(req.args.topic_name);

          if (winner_pid > 0) {
            WatchedBridge wb;
            wb.pid = winner_pid;
            wb.req = req;
            watched_bridges_[req.args.topic_name] = wb;
          } else {
            should_restart = true;
          }
        } else if (exit_code != 0) {
          std::cerr << "[BridgeGenerator] Bridge (PID: " << pid << ") crashed with code "
                    << exit_code << ". Restarting..." << std::endl;
          should_restart = true;
        }

      } else if (WIFSIGNALED(status)) {
        std::cerr << "[BridgeGenerator] Bridge (PID: " << pid << ") killed by signal "
                  << WTERMSIG(status) << ". Restarting..." << std::endl;
        should_restart = true;
      }

      if (should_restart && !shutdown_requested_) {
        generate_bridge(req);
      }
    }
  }
}

}  // namespace agnocast
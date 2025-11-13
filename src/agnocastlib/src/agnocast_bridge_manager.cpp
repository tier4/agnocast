#include "agnocast/agnocast_bridge_manager.hpp"

#include <rclcpp/rclcpp.hpp>

#include <fcntl.h>
#include <signal.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cerrno>
#include <cstring>
#include <stdexcept>

constexpr long MAX_MSG = 10;
constexpr int MAX_EVENTS = 10;
constexpr int WHILE_POLL_DELAY_MS = 1000;

namespace agnocast
{
std::atomic<bool> BridgeManager::running_(true);

BridgeManager::BridgeManager()
: mq_((mqd_t)-1), epoll_fd_(-1), mq_name_str_(create_mq_name_for_bridge())
{
  try {
    setup_signal_handlers();
    setup_message_queue();
    setup_epoll();

    RCLCPP_INFO(logger, "[BRIDGE MANAGER] PID: %d", getpid());
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger, "BridgeManager initialization failed: %s", e.what());
    throw;
  }
}

BridgeManager::~BridgeManager()
{
  if (epoll_fd_ != -1) {
    close(epoll_fd_);
    epoll_fd_ = -1;
  }

  if (mq_ != (mqd_t)-1) {
    mq_close(mq_);
    mq_ = (mqd_t)-1;
  }
  if (!mq_name_str_.empty()) {
    mq_unlink(mq_name_str_.c_str());
  }
}

void BridgeManager::run()
{
  struct epoll_event events[MAX_EVENTS];

  while (running_) {
    int num_events = epoll_wait(epoll_fd_, events, MAX_EVENTS, WHILE_POLL_DELAY_MS);

    if (num_events < 0 && errno == EINTR) {
      continue;
    } else if (num_events < 0) {
      RCLCPP_ERROR(logger, "epoll_wait() failed: %s", strerror(errno));
      break;
    }

    for (int i = 0; i < num_events; i++) {
      if (events[i].data.fd != mq_) {
        continue;
      }

      MqMsgBridge req;
      if (mq_receive(mq_, reinterpret_cast<char *>(&req), sizeof(MqMsgBridge), nullptr) < 0) {
        RCLCPP_WARN(logger, "mq_receive failed: %s", strerror(errno));
        continue;
      }

      handle_bridge_request(req);
    }

    if (num_events == 0) {
      check_and_remove_bridges();
      check_and_request_shutdown();
    }
  }
}

void BridgeManager::setup_message_queue()
{
  const char * mq_name = mq_name_str_.c_str();
  struct mq_attr attr{};
  attr.mq_maxmsg = MAX_MSG;
  attr.mq_msgsize = sizeof(MqMsgBridge);

  mq_unlink(mq_name);

  mq_ = mq_open(mq_name, O_CREAT | O_RDONLY, 0644, &attr);
  if (mq_ == (mqd_t)-1) {
    throw std::runtime_error("mq_open failed: " + std::string(strerror(errno)));
  }
}

void BridgeManager::setup_epoll()
{
  epoll_fd_ = epoll_create1(0);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed: " + std::string(strerror(errno)));
  }

  struct epoll_event ev{};
  ev.events = EPOLLIN;
  ev.data.fd = mq_;

  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_, &ev) == -1) {
    close(epoll_fd_);
    throw std::runtime_error("epoll_ctl failed to add mq: " + std::string(strerror(errno)));
  }
}

void BridgeManager::setup_signal_handlers()
{
  std::signal(SIGPIPE, SIG_IGN);

  struct sigaction sa;
  sa.sa_handler = sigchld_handler;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART | SA_NOCLDSTOP;

  if (sigaction(SIGCHLD, &sa, 0) == -1) {
    throw std::runtime_error("Failed to register SIGCHLD handler");
  }

  struct sigaction sa_shutdown;
  sa_shutdown.sa_handler = shutdown_handler;
  sigemptyset(&sa_shutdown.sa_mask);
  sa_shutdown.sa_flags = 0;

  if (sigaction(SIGINT, &sa_shutdown, 0) == -1) {
    throw std::runtime_error("Failed to register SIGINT handler");
  }
  if (sigaction(SIGTERM, &sa_shutdown, 0) == -1) {
    throw std::runtime_error("Failed to register SIGTERM handler");
  }
}

void BridgeManager::sigchld_handler([[maybe_unused]] int sig)
{
  while (waitpid(-1, NULL, WNOHANG) > 0);
}

void BridgeManager::shutdown_handler([[maybe_unused]] int sig)
{
  running_.store(false);
}

std::vector<agnocast::BridgeManager::ActiveBridge> & BridgeManager::get_bridge_list(
  BridgeDirection direction)
{
  if (direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    return active_r2a_bridges_;
  } else {
    return active_a2r_bridges_;
  }
}

bool BridgeManager::does_bridge_exist(BridgeDirection direction, const std::string & topic_name)
{
  std::lock_guard<std::mutex> lock(bridges_mutex_);

  auto & bridge_list = get_bridge_list(direction);
  auto topic_matches = [&](const ActiveBridge & bridge) { return bridge.topic_name == topic_name; };

  return std::any_of(bridge_list.begin(), bridge_list.end(), topic_matches);
}

void BridgeManager::handle_bridge_request(const MqMsgBridge & req)
{
  const std::string topic_name_str(req.args.topic_name);

  if (does_bridge_exist(req.direction, topic_name_str)) {
    return;
  }

  pid_t pid = fork();

  if (pid < 0) {
    RCLCPP_ERROR(logger, "fork failed: %s", strerror(errno));
    return;
  }

  if (pid == 0) {
    if (setsid() == -1) {
      RCLCPP_ERROR(logger, "setsid failed for unlink manager: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    bridge_process_main(req);
    exit(EXIT_SUCCESS);
  }

  {
    std::lock_guard<std::mutex> lock(bridges_mutex_);
    ActiveBridge new_bridge = {pid, topic_name_str};

    auto & bridge_list = get_bridge_list(req.direction);
    bridge_list.push_back(new_bridge);

    RCLCPP_INFO(logger, "Launched new bridge PID %d for topic %s", pid, req.args.topic_name);
  }
}

void BridgeManager::remove_bridges(
  std::vector<ActiveBridge> & bridges, std::function<bool(const std::string &)> check_demand)
{
  bridges.erase(
    std::remove_if(
      bridges.begin(), bridges.end(),
      [&](ActiveBridge & bridge) {
        if (kill(bridge.pid, 0) == -1 && errno == ESRCH) {
          return true;
        }

        if (!check_demand(bridge.topic_name)) {
          kill(bridge.pid, SIGTERM);
          return true;
        }

        return false;
      }),
    bridges.end());
}

bool BridgeManager::check_r2a_demand(const std::string & topic_name) const
{
  return check_demand_internal<union ioctl_get_ext_subscriber_num_args>(
    topic_name, active_a2r_bridges_, AGNOCAST_GET_EXT_SUBSCRIBER_NUM_CMD,
    [](const union ioctl_get_ext_subscriber_num_args & args) {
      return args.ret_ext_subscriber_num;
    });
}

bool BridgeManager::check_a2r_demand(const std::string & topic_name) const
{
  return check_demand_internal<union ioctl_get_ext_publisher_num_args>(
    topic_name, active_r2a_bridges_, AGNOCAST_GET_EXT_PUBLISHER_NUM_CMD,
    [](const union ioctl_get_ext_publisher_num_args & args) { return args.ret_ext_publisher_num; });
}

void BridgeManager::check_and_remove_bridges()
{
  std::lock_guard<std::mutex> lock(bridges_mutex_);

  remove_bridges(active_r2a_bridges_, [&](const std::string & topic_name) {
    return check_r2a_demand(topic_name);
  });

  remove_bridges(active_a2r_bridges_, [&](const std::string & topic_name) {
    return check_a2r_demand(topic_name);
  });
}

void BridgeManager::check_and_request_shutdown()
{
  struct ioctl_get_active_process_num_args args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_ACTIVE_PROCESS_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger, "Failed to get active process count from kernel module.");
    return;
  }

  if (args.ret_active_process_num <= 1) {
    std::lock_guard<std::mutex> lock(bridges_mutex_);
    if (active_r2a_bridges_.empty() && active_a2r_bridges_.empty()) {
      running_.store(false);
    }
  }
}

}  // namespace agnocast
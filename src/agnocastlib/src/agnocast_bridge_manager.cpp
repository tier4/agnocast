#include "agnocast/agnocast_bridge_manager.hpp"

// #include "agnocast/agnocast_callback_isolated_executor.hpp"
// #include "agnocast/agnocast_multi_threaded_executor.hpp"
// #include "agnocast/agnocast_single_threaded_executor.hpp"

#include <dlfcn.h>
#include <fcntl.h>  // open 用
#include <signal.h>
#include <sys/epoll.h>
#include <sys/wait.h>
#include <unistd.h>
#include <unistd.h>  // dup2, close 用

#include <cerrno>
#include <cstring>

extern "C" bool agnocast_heaphook_init_daemon();

constexpr long MAX_MSG = 10;
constexpr int MAX_EVENTS = 10;
constexpr int WHILE_POLL_DELAY_MS = 1000;
constexpr pid_t NO_OPPOSITE_BRIDGE_PID = -1;

namespace agnocast
{
std::atomic<bool> BridgeManager::running_(true);

BridgeManager::BridgeManager()
: mq_((mqd_t)-1), epoll_fd_(-1), mq_name_str_(create_mq_name_for_bridge())
{
  try {
    std::signal(SIGPIPE, SIG_IGN);

    struct sigaction sa;
    sa.sa_handler = sigchld_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART | SA_NOCLDSTOP;
    if (sigaction(SIGCHLD, &sa, 0) == -1) {
      throw std::runtime_error("Failed to register SIGCHLD handler");
    }

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
  // ログファイルを開く (例: /tmp/bridge_PID.log)
  std::string log_path = "/tmp/agnocast_bridge.log";
  int log_fd = open(log_path.c_str(), O_RDWR | O_CREAT | O_APPEND, 0644);

  if (log_fd != -1) {
    // 標準出力(fd=1) と 標準エラー(fd=2) をログファイルに向ける
    dup2(log_fd, STDOUT_FILENO);
    dup2(log_fd, STDERR_FILENO);
    // 元の log_fd は不要なので閉じる
    close(log_fd);
  } else {
    // ログファイルが開けなかった (致命的ではないが進める)
    // (この場合、出力は /dev/null に向かう可能性が高い)
  }

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
      if (mq_receive(mq_, (char *)&req, sizeof(MqMsgBridge), NULL) < 0) {
        RCLCPP_WARN(logger, "mq_receive failed: %s", strerror(errno));
        continue;
      }

      handle_bridge_request(req);
    }

    check_and_remove_bridges();

    RCLCPP_INFO(logger, "TEST 10");

    check_and_request_shutdown();
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

void BridgeManager::sigchld_handler(int sig)
{
  (void)sig;
  while (waitpid(-1, NULL, WNOHANG) > 0);
}

bool BridgeManager::does_bridge_exist(const MqMsgBridge & req) const
{
  std::lock_guard<std::mutex> lock(bridges_mutex_);

  const std::string topic_name_str(req.args.topic_name);
  auto topic_matches = [&](const ActiveBridge & bridge) {
    return bridge.topic_name == topic_name_str;
  };

  if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    return std::any_of(active_r2a_bridges_.begin(), active_r2a_bridges_.end(), topic_matches);
  } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
    return std::any_of(active_a2r_bridges_.begin(), active_a2r_bridges_.end(), topic_matches);
  }
  return false;
}

void BridgeManager::handle_bridge_request(const MqMsgBridge & req)
{
  if (does_bridge_exist(req)) {
    return;
  }

  pid_t pid = fork();

  if (pid < 0) {
    RCLCPP_ERROR(logger, "fork failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  if (pid == 0) {
    if (setsid() == -1) {
      RCLCPP_ERROR(logger, "setsid failed for unlink daemon: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    RCLCPP_INFO(logger, "[BRIDGE PROCESS] PID: %d", getpid());

    if (!agnocast_heaphook_init_daemon()) {
      RCLCPP_ERROR(logger, "Heaphook init FAILED.");
    }

    bridge_process_main(req);
    exit(EXIT_SUCCESS);
  }

  {
    std::lock_guard<std::mutex> lock(bridges_mutex_);
    ActiveBridge new_bridge = {pid, std::string(req.args.topic_name)};

    if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
      active_r2a_bridges_.push_back(new_bridge);
      RCLCPP_INFO(logger, "Puhs R2A");
    } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
      active_a2r_bridges_.push_back(new_bridge);
    }
    RCLCPP_INFO(logger, "Launched new bridge PID %d for topic %s", pid, req.args.topic_name);
  }
}

bool BridgeManager::check_r2a_demand(const std::string & topic_name) const
{
  pid_t opposite_pid = NO_OPPOSITE_BRIDGE_PID;

  auto it = std::find_if(
    active_a2r_bridges_.begin(), active_a2r_bridges_.end(),
    [&](const ActiveBridge & bridge) { return bridge.topic_name == topic_name; });

  if (it != active_a2r_bridges_.end()) {
    opposite_pid = it->pid;
  }

  RCLCPP_INFO(logger, "EXT_PID = %d", opposite_pid);

  union ioctl_get_ext_subscriber_num_args args = {};
  args.topic_name = {topic_name.c_str(), topic_name.size()};
  args.exclude_pid = opposite_pid;

  if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_SUBSCRIBER_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger, "Failed to get ext sub count for '%s'", topic_name.c_str());
    return false;
  }

  auto sub_num = args.ret_ext_subscriber_num;
  RCLCPP_INFO(logger, "SUB_NUM = %d", sub_num);

  return args.ret_ext_subscriber_num > 0;
}

bool BridgeManager::check_a2r_demand(const std::string & topic_name) const
{
  pid_t opposite_pid = NO_OPPOSITE_BRIDGE_PID;

  auto it = std::find_if(
    active_r2a_bridges_.begin(), active_r2a_bridges_.end(),
    [&](const ActiveBridge & bridge) { return bridge.topic_name == topic_name; });

  if (it != active_r2a_bridges_.end()) {
    opposite_pid = it->pid;
  }

  union ioctl_get_ext_publisher_num_args args = {};
  args.topic_name = {topic_name.c_str(), topic_name.size()};
  args.exclude_pid = opposite_pid;
  if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_PUBLISHER_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger, "Failed to get ext pub count for '%s'", topic_name.c_str());
    return false;
  }
  return args.ret_ext_publisher_num > 0;
}

void BridgeManager::check_and_remove_bridges()
{
  std::lock_guard<std::mutex> lock(bridges_mutex_);

  RCLCPP_INFO(logger, "Start remove check");

  active_r2a_bridges_.erase(
    std::remove_if(
      active_r2a_bridges_.begin(), active_r2a_bridges_.end(),
      [&](ActiveBridge & bridge) {
        if (kill(bridge.pid, 0) == -1 && errno == ESRCH) {
          RCLCPP_INFO(logger, "Kill 1");
          return true;
        }

        if (!check_r2a_demand(bridge.topic_name)) {
          kill(bridge.pid, SIGTERM);
          RCLCPP_INFO(logger, "Kill 2");
          return true;
        }

        RCLCPP_INFO(logger, "Not Kill");
        return false;
      }),
    active_r2a_bridges_.end());

  active_a2r_bridges_.erase(
    std::remove_if(
      active_a2r_bridges_.begin(), active_a2r_bridges_.end(),
      [&](ActiveBridge & bridge) {
        if (kill(bridge.pid, 0) == -1 && errno == ESRCH) {
          return true;
        }

        if (!check_a2r_demand(bridge.topic_name)) {
          kill(bridge.pid, SIGTERM);
          return true;
        }

        return false;
      }),
    active_a2r_bridges_.end());
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
      RCLCPP_INFO(logger, "Shutdown");
    } else {
      RCLCPP_INFO(logger, "Not shutdown");
    }
  } else {
    RCLCPP_INFO(logger, "Not Process one");
  }
}

}  // namespace agnocast
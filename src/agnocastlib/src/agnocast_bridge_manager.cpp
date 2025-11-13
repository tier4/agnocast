#include "agnocast/agnocast_bridge_manager.hpp"

// #include "agnocast/agnocast_callback_isolated_executor.hpp"
// #include "agnocast/agnocast_multi_threaded_executor.hpp"
// #include "agnocast/agnocast_single_threaded_executor.hpp"

#include <dlfcn.h>
#include <signal.h>
#include <sys/epoll.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>

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
    setup_message_queue();
    setup_epoll();

    RCLCPP_INFO(logger, "PID: %d", getpid());
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

    RCLCPP_INFO(logger, "epoll_wait returned %d events", num_events);

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

      handle_bridge_request();
    }

    // check_and_remove_bridges();
    // cleanup_finished_futures();
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

void BridgeManager::cleanup_finished_futures()
{
  // todo
}

bool BridgeManager::does_bridge_exist() const
{
  // todo
  return false;
}

void BridgeManager::handle_bridge_request()
{
  RCLCPP_INFO(logger, "Handling bridge request for topic");
  // if (does_bridge_exist(req)) {
  //   return;
  // }

  // if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
  //   worker_futures_.push_back(
  //     std::async(std::launch::async, &BridgeManager::launch_r2a_bridge_thread, this, req));
  // } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
  //   worker_futures_.push_back(
  //     std::async(std::launch::async, &BridgeManager::launch_a2r_bridge_thread, this, req));
  // }
}

bool BridgeManager::check_r2a_demand(const std::string & topic_name, pid_t self_pid) const
{
  union ioctl_get_ext_subscriber_num_args args = {};
  args.topic_name = {topic_name.c_str(), topic_name.size()};
  args.exclude_pid = self_pid;
  if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_SUBSCRIBER_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger, "Failed to get ext sub count for '%s'", topic_name.c_str());
    return false;
  }
  return args.ret_ext_subscriber_num > 0;
}

bool BridgeManager::check_a2r_demand(const std::string & topic_name, pid_t self_pid) const
{
  union ioctl_get_ext_publisher_num_args args = {};
  args.topic_name = {topic_name.c_str(), topic_name.size()};
  args.exclude_pid = self_pid;
  if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_PUBLISHER_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger, "Failed to get ext pub count for '%s'", topic_name.c_str());
    return false;
  }
  return args.ret_ext_publisher_num > 0;
}

void BridgeManager::check_and_remove_bridges()
{
  // const pid_t self_pid = getpid();

  // todo
}

void BridgeManager::check_and_request_shutdown()
{
  struct ioctl_get_active_process_num_args args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_ACTIVE_PROCESS_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger, "Failed to get active process count from kernel module.");
    return;
  }

  RCLCPP_INFO(logger, "TEST1");

  if (args.ret_active_process_num <= 1) {
    RCLCPP_INFO(logger, "TEST2");
    running_.store(false);
  }
}

}  // namespace agnocast
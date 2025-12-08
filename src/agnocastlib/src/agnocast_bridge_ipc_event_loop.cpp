#include "agnocast/agnocast_bridge_ipc_event_loop.hpp"

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cerrno>
#include <system_error>

namespace agnocast
{

constexpr long MQ_MAX_MSG = 10;
constexpr long MQ_MSG_SIZE = sizeof(MqMsgBridge);
constexpr mode_t MQ_PERMS = 0600;

BridgeIpcEventLoop::BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger & logger)
: logger_(logger)
{
  try {
    setup_mq(target_pid);
    // TODO:: signal, epoll setup will be implemented in following PRs
  } catch (...) {
    cleanup_resources();
    throw;
  }
}

BridgeIpcEventLoop::~BridgeIpcEventLoop()
{
  cleanup_resources();
}

void BridgeIpcEventLoop::cleanup_resources()
{
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
}

void BridgeIpcEventLoop::setup_mq(pid_t target_pid)
{
  auto create_and_open = [](const std::string & name, const std::string & label) -> mqd_t {
    struct mq_attr attr
    {
    };
    attr.mq_maxmsg = MQ_MAX_MSG;
    attr.mq_msgsize = MQ_MSG_SIZE;

    mq_unlink(name.c_str());

    mqd_t fd = mq_open(name.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK | O_CLOEXEC, MQ_PERMS, &attr);

    if (fd == (mqd_t)-1) {
      throw std::system_error(errno, std::generic_category(), label + " MQ open failed");
    }
    return fd;
  };

  mq_parent_name_ = create_mq_name_for_bridge_parent(target_pid);
  mq_parent_fd_ = create_and_open(mq_parent_name_, "Parent");

  mq_child_name_ = create_mq_name_for_bridge_child(getpid());
  mq_child_fd_ = create_and_open(mq_child_name_, "Child");
}

}  // namespace agnocast

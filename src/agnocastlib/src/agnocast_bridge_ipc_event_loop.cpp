#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"

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

BridgeIpcEventLoop::BridgeIpcEventLoop(pid_t target_pid, const rclcpp::Logger & logger)
: logger_(logger)
{
  setup_mq(target_pid);
  setup_signals();
  setup_epoll();
}

BridgeIpcEventLoop::~BridgeIpcEventLoop()
{
  // TODO: Define helper lambdas `close_fd` and `close_and_unlink_mq`
  // TODO: Close and unlink parent/child MQs using helpers
  // TODO: Close `epoll_fd_` and `signal_fd_` using helpers
}

void BridgeIpcEventLoop::set_parent_mq_handler(EventCallback cb)
{
  // TODO: Store callback for parent MQ events
}
void BridgeIpcEventLoop::set_child_mq_handler(EventCallback cb)
{
  // TODO: Store callback for child MQ events
}
void BridgeIpcEventLoop::set_signal_handler(SignalCallback cb)
{
  // TODO: Store callback for signal events
}

bool BridgeIpcEventLoop::spin_once(int timeout_ms)
{
  // TODO: Call `epoll_wait` to wait for events

  // TODO: Iterate through triggered events:
  //   - If fd == mq_parent_fd_: execute `parent_cb_`
  //   - If fd == mq_child_fd_: execute `child_cb_`
  //   - If fd == signal_fd_: `read` signal info and execute `signal_cb_`

  return true;  // or false on error
}

void BridgeIpcEventLoop::close_parent_mq()
{
  // TODO: If MQ is valid, remove from epoll (`epoll_ctl` with `EPOLL_CTL_DEL`)
  // TODO: Close (`mq_close`) and unlink (`mq_unlink`) the MQ
}

void BridgeIpcEventLoop::setup_mq(pid_t target_pid)
{
  // TODO: Define helper lambda `create_and_open`
  // TODO: Generate name and open Parent MQ (`create_mq_name_for_bridge_parent`)
  // TODO: Generate name and open Child MQ (`create_mq_name_for_bridge_child`)
}

void BridgeIpcEventLoop::setup_signals()
{
  // TODO: Ignore SIGPIPE, SIGHUP (`::signal`)
  // TODO: Block SIGTERM, SIGINT (`sigprocmask`)
  // TODO: Create signal file descriptor (`signalfd`)
}

void BridgeIpcEventLoop::setup_epoll()
{
  // TODO: Create epoll instance (`epoll_create1`)
  // TODO: Add `mq_parent_fd_`, `mq_child_fd_`, and `signal_fd_` to epoll instance (`epoll_ctl`)
}

}  // namespace agnocast

#pragma GCC diagnostic pop

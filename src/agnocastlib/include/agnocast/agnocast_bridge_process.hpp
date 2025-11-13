#pragma once

#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>

#include <memory>

using DlClosePtrType = int (*)(void *);
using DlHandlePtr = std::unique_ptr<void, DlClosePtrType>;

namespace agnocast
{

class BridgeProcess
{
public:
  explicit BridgeProcess(const MqMsgBridge & req);

  ~BridgeProcess() = default;

  void run();

private:
  static void bridge_signal_handler(int signum);
  void setup_signal_handlers();
  void load_bridge_function();

  const MqMsgBridge & req_;
  rclcpp::Logger logger_;
  BridgeFn entry_func_ = nullptr;
  DlHandlePtr dl_handle_{nullptr, &dlclose};
};

}  // namespace agnocast

#include "agnocast/agnocast_bridge_process.hpp"

extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

BridgeProcess::BridgeProcess(const MqMsgBridge & req)
: req_(req), logger_(rclcpp::get_logger("agnocast_bridge_daemon"))
{
  RCLCPP_INFO(logger_, "[BRIDGE PROCESS] PID: %d", getpid());

  if (!agnocast_heaphook_init_daemon()) {
    RCLCPP_ERROR(logger_, "Heaphook init FAILED.");
  }

  setup_signal_handlers();
  load_bridge_function();
}

void BridgeProcess::bridge_signal_handler([[maybe_unused]] int signum)
{
  rclcpp::shutdown();
}

void BridgeProcess::setup_signal_handlers()
{
  struct sigaction sa_pipe;
  sa_pipe.sa_handler = SIG_IGN;
  sigemptyset(&sa_pipe.sa_mask);
  sa_pipe.sa_flags = 0;
  sigaction(SIGPIPE, &sa_pipe, nullptr);

  struct sigaction sa_shutdown;
  sa_shutdown.sa_handler = bridge_signal_handler;
  sigemptyset(&sa_shutdown.sa_mask);
  sa_shutdown.sa_flags = 0;
  sigaction(SIGTERM, &sa_shutdown, nullptr);
  sigaction(SIGINT, &sa_shutdown, nullptr);
}

void BridgeProcess::load_bridge_function()
{
  if (req_.fn_ptr == 0) {
    RCLCPP_FATAL(logger_, "Received a null function pointer!");
    throw std::runtime_error("Null function pointer received");
  }

  if (std::strcmp(req_.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    entry_func_ = reinterpret_cast<BridgeFn>(req_.fn_ptr);
  } else {
    const char * lib_path = req_.shared_lib_path;
    void * handle = dlopen(lib_path, RTLD_NOW);
    dl_handle_.reset(handle);

    if (!handle) {
      RCLCPP_FATAL(logger_, "dlopen failed for %s: %s", lib_path, dlerror());
      throw std::runtime_error("dlopen failed");
    }

    void * raw_func = dlsym(handle, req_.symbol_name);
    if (!raw_func) {
      RCLCPP_FATAL(
        logger_, "dlsym failed for symbol %s in %s: %s", req_.symbol_name, lib_path, dlerror());
      throw std::runtime_error("dlsym failed");
    }
    entry_func_ = reinterpret_cast<BridgeFn>(raw_func);
  }
}

void BridgeProcess::run()
{
  agnocast::SingleThreadedAgnocastExecutor executor;
  try {
    auto node = entry_func_(req_.args);
    executor.add_node(node);
    executor.spin();
  } catch (const std::exception & e) {
    RCLCPP_FATAL(
      logger_, "Unhandled std::exception: %s for topic: %s", e.what(), req_.args.topic_name);
  } catch (...) {
    RCLCPP_FATAL(logger_, "Unhandled unknown exception for topic: %s", req_.args.topic_name);
  }
}

}  // namespace agnocast

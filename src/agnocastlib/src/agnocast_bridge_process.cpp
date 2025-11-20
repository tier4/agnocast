#include "agnocast/agnocast_bridge_process.hpp"

#include "agnocast/agnocast_single_threaded_executor.hpp"

extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

BridgeProcess::BridgeProcess(const MqMsgBridge & req)
: req_(req), logger_(rclcpp::get_logger("agnocast_bridge_process"))
{
  RCLCPP_INFO(logger_, "[BRIDGE PROCESS] PID: %d", getpid());

  if (!agnocast_heaphook_init_daemon()) {
    RCLCPP_ERROR(logger_, "Heaphook init FAILED.");
  }

  setup_signal_handlers();
  load_bridge_function();
}

void BridgeProcess::setup_signal_handlers()
{
  struct sigaction sa;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = 0;

  sa.sa_handler = SIG_IGN;
  sigaction(SIGPIPE, &sa, nullptr);

  sa.sa_handler = [](int /*signum*/) { rclcpp::shutdown(); };

  sigaction(SIGTERM, &sa, nullptr);
  sigaction(SIGINT, &sa, nullptr);
}

void BridgeProcess::load_bridge_function()
{
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

#include "agnocast/agnocast_bridge_node.hpp"

#include "agnocast/agnocast.hpp"

#include <dlfcn.h>
#include <signal.h>

extern int agnocast_fd;
extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

QoSFlat flatten_qos(const rclcpp::QoS & qos)
{
  QoSFlat out{};
  const auto & rmw_qos = qos.get_rmw_qos_profile();
  out.depth = rmw_qos.depth;
  out.history = (rmw_qos.history == RMW_QOS_POLICY_HISTORY_KEEP_ALL) ? 1 : 0;
  out.reliability = (rmw_qos.reliability == RMW_QOS_POLICY_RELIABILITY_RELIABLE) ? 1 : 2;
  out.durability = (rmw_qos.durability == RMW_QOS_POLICY_DURABILITY_TRANSIENT_LOCAL) ? 1 : 2;
  return out;
}

rclcpp::QoS reconstruct_qos(const QoSFlat & q)
{
  rclcpp::QoS qos(q.depth);
  if (q.history == 1) {
    qos.keep_all();
  }
  if (q.reliability == 1) {
    qos.reliable();
  } else if (q.reliability == 2) {
    qos.best_effort();
  }
  if (q.durability == 1) {
    qos.transient_local();
  }
  return qos;
}

void bridge_signal_handler([[maybe_unused]] int signum)
{
  rclcpp::shutdown();
}

void bridge_process_main(const MqMsgBridge & req)
{
  rclcpp::init(0, nullptr);
  agnocast::SingleThreadedAgnocastExecutor executor;
  auto logger = rclcpp::get_logger("agnocast_bridge_daemon");

  RCLCPP_INFO(logger, "[BRIDGE PROCESS] PID: %d", getpid());

  if (!agnocast_heaphook_init_daemon()) {
    RCLCPP_ERROR(logger, "Heaphook init FAILED.");
  }

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

  if (req.fn_ptr == 0) {
    RCLCPP_FATAL(logger, "Received a null function pointer!");
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  BridgeFn entry_func = nullptr;
  void * handle = nullptr;

  if (std::strcmp(req.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    entry_func = reinterpret_cast<BridgeFn>(req.fn_ptr);
  } else {
    const char * lib_path = req.shared_lib_path;
    handle = dlopen(lib_path, RTLD_NOW);

    if (!handle) {
      RCLCPP_FATAL(logger, "dlopen failed for %s: %s", lib_path, dlerror());
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }
    void * raw_func = dlsym(handle, req.symbol_name);

    if (!raw_func) {
      RCLCPP_FATAL(
        logger, "dlsym failed for symbol %s in %s: %s", req.symbol_name, lib_path, dlerror());
      dlclose(handle);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }

    entry_func = reinterpret_cast<BridgeFn>(raw_func);
  }

  try {
    auto node = entry_func(req.args);
    executor.add_node(node);
    executor.spin();
  } catch (const std::exception & e) {
    RCLCPP_FATAL(
      logger, "Unhandled std::exception: %s for topic: %s", e.what(), req.args.topic_name);
  } catch (...) {
    RCLCPP_FATAL(logger, "Unhandled unknown exception for topic: %s", req.args.topic_name);
  }

  if (handle) {
    dlclose(handle);
  }

  rclcpp::shutdown();
  exit(EXIT_SUCCESS);
}
}  // namespace agnocast
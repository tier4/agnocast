#include "agnocast/agnocast_bridge_node.hpp"

#include <dlfcn.h>
#include <signal.h>

extern int agnocast_fd;

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

void bridge_process_main(const MqMsgBridge & msg)
{
  std::signal(SIGPIPE, SIG_IGN);

  rclcpp::init(0, nullptr);
  rclcpp::executors::SingleThreadedExecutor executor;

  auto logger = rclcpp::get_logger("agnocast_bridge_daemon");

  if (msg.fn_ptr == 0) {
    RCLCPP_FATAL(logger, "[Bridge Process Error] Received a null function pointer!");
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  BridgeFn entry_func = nullptr;

  if (std::strcmp(msg.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    entry_func = reinterpret_cast<BridgeFn>(msg.fn_ptr);
  } else {
    const char * lib_path = msg.shared_lib_path;
    void * handle = dlopen(lib_path, RTLD_NOW);

    if (!handle) {
      RCLCPP_FATAL(logger, "[Bridge Process Error] dlopen failed for %s: %s", lib_path, dlerror());
      close(agnocast_fd);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }
    void * raw_func = dlsym(handle, msg.symbol_name);

    if (!raw_func) {
      RCLCPP_FATAL(
        logger, "[Bridge Process Error] dlsym failed for symbol %s in %s: %s", msg.symbol_name,
        lib_path, dlerror());
      dlclose(handle);
      close(agnocast_fd);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }

    entry_func = reinterpret_cast<BridgeFn>(raw_func);
  }

  try {
    auto node = entry_func(msg.args);
    executor.add_node(node);
    executor.spin();
  } catch (const std::exception & e) {
    RCLCPP_FATAL(
      logger, "[Bridge Process FATAL ERROR] Unhandled std::exception: %s for topic: %s", e.what(),
      msg.args.topic_name);
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  } catch (...) {
    RCLCPP_FATAL(
      logger, "[Bridge Process FATAL ERROR] Unhandled unknown exception for topic: %s",
      msg.args.topic_name);
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  close(agnocast_fd);
  rclcpp::shutdown();
  exit(EXIT_SUCCESS);
}
}  // namespace agnocast
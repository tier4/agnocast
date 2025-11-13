#include "agnocast/agnocast_bridge_node.hpp"

#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_bridge_process.hpp"

#include <dlfcn.h>
#include <signal.h>

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

void bridge_process_main(const MqMsgBridge & req)
{
  rclcpp::init(0, nullptr);
  int exit_code = EXIT_SUCCESS;

  auto logger = rclcpp::get_logger("agnocast_bridge_bootstrap");

  try {
    BridgeProcess bridge(req);
    bridge.run();
  } catch (const std::exception & e) {
    RCLCPP_FATAL(logger, "Bridge process failed during initialization: %s", e.what());
    exit_code = EXIT_FAILURE;
  } catch (...) {
    RCLCPP_FATAL(logger, "Bridge process failed during initialization with unknown exception.");
    exit_code = EXIT_FAILURE;
  }

  rclcpp::shutdown();
  exit(exit_code);
}

}  // namespace agnocast
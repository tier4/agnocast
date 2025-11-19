#include "agnocast/agnocast_bridge_utils.hpp"

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

rclcpp::QoS get_qos_from_args(const BridgeArgs & args)
{
  rclcpp::QoS qos(args.qos.depth);

  if (args.qos.history == 1) {
    qos.keep_all();
  }
  if (args.qos.reliability == 1) {
    qos.reliable();
  } else if (args.qos.reliability == 2) {
    qos.best_effort();
  }
  if (args.qos.durability == 1) {
    qos.transient_local();
  }

  return qos;
}

void safe_strncpy(char * dest, const char * src, size_t dest_size)
{
  if (dest_size == 0) return;
  if (src == nullptr) {
    dest[0] = '\0';
    return;
  }
  std::strncpy(dest, src, dest_size - 1);
  dest[dest_size - 1] = '\0';
}

}  // namespace agnocast
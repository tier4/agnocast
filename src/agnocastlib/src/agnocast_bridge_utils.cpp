#include "agnocast/agnocast_bridge_utils.hpp"

namespace agnocast
{
QoSFlat flatten_qos(const rclcpp::QoS & qos)
{
  QoSFlat out{};
  const auto & rmw_qos = qos.get_rmw_qos_profile();
  out.depth = rmw_qos.depth;

  out.history = (rmw_qos.history == RMW_QOS_POLICY_HISTORY_KEEP_ALL) ? 1 : 0;

  if (rmw_qos.reliability == RMW_QOS_POLICY_RELIABILITY_RELIABLE) {
    out.reliability = 1;
  } else if (rmw_qos.reliability == RMW_QOS_POLICY_RELIABILITY_BEST_EFFORT) {
    out.reliability = 2;
  } else {
    out.reliability = 0;
  }

  if (rmw_qos.durability == RMW_QOS_POLICY_DURABILITY_TRANSIENT_LOCAL) {
    out.durability = 1;
  } else {
    out.durability = 0;
  }

  return out;
}

rclcpp::QoS reconstruct_qos_from_flat(const QoSFlat & flat_qos)
{
  rclcpp::QoS qos(flat_qos.depth);

  if (flat_qos.history == 1) {
    qos.keep_all();
  }

  if (flat_qos.reliability == 1) {
    qos.reliable();
  } else if (flat_qos.reliability == 2) {
    qos.best_effort();
  }

  if (flat_qos.durability == 1) {
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
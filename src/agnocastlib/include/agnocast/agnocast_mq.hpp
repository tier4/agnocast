#pragma once

#define MAX_PATH_LEN 256
#include "rclcpp/qos.hpp"

namespace agnocast
{

struct MqMsgAgnocast
{
};

struct MqMsgROS2Publish
{
  bool should_terminate;
};

struct QoSFlat
{
  uint32_t depth;
  uint8_t history;
  uint8_t reliability;
  uint8_t durability;
};

struct BridgeArgs
{
  char topic_name[256];
  QoSFlat qos;
};

struct MqMsgBridge
{
  char shared_lib_path[MAX_PATH_LEN];
  char symbol_name[MAX_PATH_LEN];
  uintptr_t fn_ptr;
  BridgeArgs args;
};

inline QoSFlat flatten_qos(const rclcpp::QoS & qos)
{
  QoSFlat out{};
  const auto & rmw_qos = qos.get_rmw_qos_profile();
  out.depth = rmw_qos.depth;
  out.history = (rmw_qos.history == RMW_QOS_POLICY_HISTORY_KEEP_ALL) ? 1 : 0;
  out.reliability = (rmw_qos.reliability == RMW_QOS_POLICY_RELIABILITY_RELIABLE) ? 1 : 2;
  out.durability = (rmw_qos.durability == RMW_QOS_POLICY_DURABILITY_TRANSIENT_LOCAL) ? 1 : 2;
  return out;
}

inline rclcpp::QoS reconstruct_qos(const QoSFlat & q)
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

}  // namespace agnocast
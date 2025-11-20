#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <sys/ioctl.h>
#include <sys/types.h>

#include <cstring>

namespace agnocast
{

extern int agnocast_fd;

QoSFlat flatten_qos(const rclcpp::QoS & qos);
rclcpp::QoS reconstruct_qos_from_flat(const QoSFlat & flat_qos);
void safe_strncpy(char * dest, const char * src, size_t dest_size);
bool check_r2a_demand(const char * topic_name, pid_t bridge_pid);
bool check_a2r_demand(const char * topic_name, pid_t bridge_pid);
void unregister_bridge(pid_t pid, const char * topic_name);

template <typename IoctlArgs, typename ResultExtractor>
bool check_demand_impl(
  unsigned long cmd, const char * topic_name, pid_t bridge_pid, ResultExtractor extractor)
{
  IoctlArgs args = {};

  args.topic_name.ptr = topic_name;
  args.topic_name.len = std::strlen(topic_name);
  args.exclude_pid = bridge_pid;

  if (ioctl(agnocast_fd, cmd, &args) < 0) {
    return false;
  }
  return extractor(args);
}

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const BridgeArgs &);

}  // namespace agnocast

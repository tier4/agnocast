#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <sys/ioctl.h>
#include <sys/types.h>

#include <cstring>

namespace agnocast
{

extern int agnocast_fd;

void safe_strncpy(char * dest, const char * src, size_t dest_size);
void unregister_bridge(pid_t pid, const char * topic_name);

using BridgeFn = std::shared_ptr<void> (*)(rclcpp::Node::SharedPtr, const BridgeTargetInfo &);

}  // namespace agnocast

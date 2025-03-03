#pragma once

#include "agnocast/agnocast_ioctl.hpp"
#include "rclcpp/rclcpp.hpp"

#include <string>

namespace agnocast
{

extern rclcpp::Logger logger;

void validate_ld_preload();
std::string create_mq_name_for_agnocast_publish(
  const std::string & topic_name, const topic_local_id_t id);
std::string create_mq_name_for_ros2_publish(
  const std::string & topic_name, const topic_local_id_t id);
std::string create_shm_name(const pid_t pid);
uint64_t agnocast_get_timestamp();

}  // namespace agnocast

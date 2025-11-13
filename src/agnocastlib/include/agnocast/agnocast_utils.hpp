#pragma once

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>

#include <string>

namespace agnocast
{

extern rclcpp::Logger logger;

void validate_ld_preload();
std::string create_mq_name_for_agnocast_publish(
  const std::string & topic_name, const topic_local_id_t id);
std::string create_mq_name_for_bridge();
std::string create_shm_name(const pid_t pid);
std::string create_service_request_topic_name(const std::string & service_name);
std::string create_service_response_topic_name(
  const std::string & service_name, const std::string & client_node_name);
uint64_t agnocast_get_timestamp();

}  // namespace agnocast

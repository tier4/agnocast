#pragma once

#include "rclcpp/rclcpp.hpp"

#include <string>

namespace agnocast
{

extern rclcpp::Logger logger;

void validate_ld_preload();
std::string create_mq_name(const std::string & topic_name, const uint32_t pid);
uint64_t agnocast_get_timestamp();

}  // namespace agnocast

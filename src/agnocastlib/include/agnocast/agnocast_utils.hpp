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
std::string create_mq_name_for_ros2_publish(
  const std::string & topic_name, const topic_local_id_t id);
std::string create_mq_name_for_bridge();
std::string create_shm_name(const pid_t pid);
std::string create_service_request_topic_name(const std::string & service_name);
std::string create_service_response_topic_name(
  const std::string & service_name, const std::string & client_node_name);
uint64_t agnocast_get_timestamp();

template <typename MessageT>
void send_bridge_request(
  const std::string & topic_name, const rclcpp::QoS & qos, BridgeDirection direction)
{
  (void)qos;

  const std::string mq_name_str = create_mq_name_for_bridge();
  const char * mq_name = mq_name_str.c_str();
  mqd_t mq = mq_open(mq_name, O_WRONLY);

  if (mq == (mqd_t)-1) {
    RCLCPP_ERROR(
      logger, "Failed to open bridge manager message queue '%s'. Error: %s", mq_name,
      strerror(errno));
    return;
  }

  BridgeRequest req = {};
  const std::string message_type_name = rosidl_generator_traits::name<MessageT>();

  strncpy(req.topic_name, topic_name.c_str(), MAX_NAME_LENGTH - 1);
  strncpy(req.message_type, message_type_name.c_str(), MAX_NAME_LENGTH - 1);

  req.direction = direction;

  if (mq_send(mq, (const char *)&req, sizeof(BridgeRequest), 0) == -1) {
    RCLCPP_ERROR(
      logger, "Failed to send bridge request to manager daemon. Error: %s", strerror(errno));
  }
  mq_close(mq);
}

}  // namespace agnocast

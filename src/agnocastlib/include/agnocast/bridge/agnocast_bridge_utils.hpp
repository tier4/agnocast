#pragma once

#include "agnocast/agnocast_ioctl.hpp"

#include <rclcpp/qos.hpp>

#include <string>

namespace agnocast
{

struct SubscriberCountResult
{
  int count;          // -1 on error, otherwise the subscriber count (including bridge subscriber)
  bool bridge_exist;  // true if A2R bridge exists for this topic
};

struct PublisherCountResult
{
  int count;          // -1 on error, otherwise the publisher count (including bridge publisher)
  bool bridge_exist;  // true if R2A bridge exists for this topic
};

rclcpp::QoS get_subscriber_qos(const std::string & topic_name, topic_local_id_t subscriber_id);
rclcpp::QoS get_publisher_qos(const std::string & topic_name, topic_local_id_t publisher_id);
PublisherCountResult get_agnocast_publisher_count(const std::string & topic_name);
SubscriberCountResult get_agnocast_subscriber_count(const std::string & topic_name);

}  // namespace agnocast

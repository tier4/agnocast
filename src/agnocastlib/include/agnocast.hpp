#pragma once

#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cstring>
#include <functional>
#include <memory>
#include <sys/ioctl.h>

#include "rclcpp/rclcpp.hpp"

#include "agnocast_publisher.hpp"
#include "agnocast_subscription.hpp"

namespace agnocast {

__attribute__((constructor))
void initialize_agnocast();

template<typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(std::string topic_name, const rclcpp::QoS & qos) {
  return std::make_shared<Publisher<MessageT>>(topic_name, qos);
}

template<typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(std::string topic_name, size_t qos_history_depth) {
  return std::make_shared<Publisher<MessageT>>(topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

template<typename MessageT>
std::shared_ptr<Subscription<MessageT>> create_subscription(const char* topic_name, const rclcpp::QoS & qos, std::function<void(const agnocast::message_ptr<MessageT> &)> callback) {
  subscribe_topic_agnocast(topic_name, qos, callback);
  return std::make_shared<Subscription<MessageT>>();
}

template<typename MessageT>
std::shared_ptr<Subscription<MessageT>> create_subscription(const char* topic_name, size_t qos_history_depth, std::function<void(const agnocast::message_ptr<MessageT> &)> callback) {
  subscribe_topic_agnocast(topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback);
  return std::make_shared<Subscription<MessageT>>();
}

} // namespace agnocast

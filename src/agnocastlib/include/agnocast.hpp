#pragma once

#include "agnocast_publisher.hpp"
#include "agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstring>
#include <functional>
#include <memory>

namespace agnocast
{

void * initialize_agnocast(const uint64_t shm_size);

template <typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(
  const std::string & topic_name, const rclcpp::QoS & qos)
{
  return std::make_shared<Publisher<MessageT>>(topic_name, qos);
}

template <typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(
  const std::string & topic_name, const size_t qos_history_depth)
{
  return std::make_shared<Publisher<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

template <typename MessageT>
std::shared_ptr<Subscription<MessageT>> create_subscription(
  const std::string & topic_name, const rclcpp::QoS & qos,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  return std::make_shared<Subscription<MessageT>>(topic_name, qos, callback);
}

template <typename MessageT>
std::shared_ptr<Subscription<MessageT>> create_subscription(
  const std::string & topic_name, const size_t qos_history_depth,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  return std::make_shared<Subscription<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback);
}

template <typename MessageT>
std::shared_ptr<TakeSubscription<MessageT>> create_subscription(
  const std::string & topic_name, const rclcpp::QoS & qos)
{
  if (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
    std::cerr
      << "[Warning]: The transient local is not supported by TakeSubscription, so it is ignored."
      << std::endl;
  }
  return std::make_shared<TakeSubscription<MessageT>>(topic_name, qos);
}

template <typename MessageT>
std::shared_ptr<TakeSubscription<MessageT>> create_subscription(
  const std::string & topic_name, const size_t qos_history_depth)
{
  return std::make_shared<TakeSubscription<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

}  // namespace agnocast

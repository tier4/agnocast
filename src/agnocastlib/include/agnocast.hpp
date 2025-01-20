#pragma once

#include "agnocast_multi_threaded_executor.hpp"
#include "agnocast_publisher.hpp"
#include "agnocast_single_threaded_executor.hpp"
#include "agnocast_subscription.hpp"
#include "agnocast_topic_info.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

#include <cstring>
#include <functional>
#include <memory>

namespace agnocast
{

extern "C" void * initialize_agnocast(const uint64_t shm_size);

bool ok();

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
{
  return std::make_shared<Publisher<MessageT>>(node, topic_name, qos, true);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth)
{
  return std::make_shared<Publisher<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), true);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
  const bool do_always_ros2_publish)
{
  return std::make_shared<Publisher<MessageT>>(node, topic_name, qos, do_always_ros2_publish);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth,
  const bool do_always_ros2_publish)
{
  return std::make_shared<Publisher<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), do_always_ros2_publish);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(node, topic_name, qos, callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback,
  agnocast::SubscriptionOptions options)
{
  return std::make_shared<Subscription<MessageT>>(node, topic_name, qos, callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback,
  agnocast::SubscriptionOptions options)
{
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback, options);
}

template <typename MessageT>
typename PollingSubscriber<MessageT>::SharedPtr create_subscription(
  const std::string & topic_name, const size_t qos_history_depth)
{
  return std::make_shared<PollingSubscriber<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

template <typename MessageT>
typename PollingSubscriber<MessageT>::SharedPtr create_subscription(
  const std::string & topic_name, const rclcpp::QoS & qos)
{
  return std::make_shared<PollingSubscriber<MessageT>>(topic_name, qos);
}

}  // namespace agnocast

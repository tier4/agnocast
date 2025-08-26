#pragma once

#include "agnocast/agnocast_callback_info.hpp"
#include "agnocast/agnocast_callback_isolated_executor.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_single_threaded_executor.hpp"
#include "agnocast/agnocast_subscription.hpp"
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

extern "C" void * initialize_agnocast(
  const uint64_t shm_size, const unsigned char * heaphook_version_ptr,
  const size_t heaphook_version_str_len);

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
{
  PublisherOptions options;
  return std::make_shared<Publisher<MessageT>>(node, topic_name, qos, options);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth)
{
  PublisherOptions options;
  return std::make_shared<Publisher<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), options);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
  const PublisherOptions & options)
{
  return std::make_shared<Publisher<MessageT>>(node, topic_name, qos, options);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth,
  const PublisherOptions & options)
{
  return std::make_shared<Publisher<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), options);
}

template <typename MessageT, typename Func>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos, Func && callback)
{
  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, qos, std::forward<Func>(callback), options);
}

template <typename MessageT, typename Func>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth,
  Func && callback)
{
  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)),
    std::forward<Func>(callback), options);
}

template <typename MessageT, typename Func>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos, Func && callback,
  agnocast::SubscriptionOptions options)
{
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, qos, std::forward<Func>(callback), options);
}

template <typename MessageT, typename Func>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth,
  Func && callback, agnocast::SubscriptionOptions options)
{
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)),
    std::forward<Func>(callback), options);
}

template <typename MessageT>
typename PollingSubscriber<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const size_t qos_history_depth)
{
  return std::make_shared<PollingSubscriber<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

template <typename MessageT>
typename PollingSubscriber<MessageT>::SharedPtr create_subscription(
  rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
{
  return std::make_shared<PollingSubscriber<MessageT>>(node, topic_name, qos);
}

}  // namespace agnocast

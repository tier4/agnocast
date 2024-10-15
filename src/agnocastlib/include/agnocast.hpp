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

extern "C" void * initialize_agnocast(const uint64_t shm_size);

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  const std::string & topic_name, const rclcpp::QoS & qos)
{
  return std::make_shared<Publisher<MessageT>>(topic_name, qos);
}

template <typename MessageT>
typename Publisher<MessageT>::SharedPtr create_publisher(
  const std::string & topic_name, const size_t qos_history_depth)
{
  return std::make_shared<Publisher<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

// Backward compatibility: deprecated interface. Delete it later.
template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  const std::string & topic_name, const rclcpp::QoS & qos,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  std::cerr << "\033[0;33m"
            << "Deprecated: use the latest version of create_subscription"
            << "\033[0m" << std::endl;

  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(nullptr, topic_name, qos, callback, options);
}

// Backward compatibility: deprecated interface. Delete it later.
template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  const std::string & topic_name, const size_t qos_history_depth,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  std::cerr << "\033[0;33m"
            << "Deprecated: use the latest version of create_subscription"
            << "\033[0m" << std::endl;

  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(
    nullptr, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node, const std::string & topic_name,
  const rclcpp::QoS & qos, std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(node, topic_name, qos, callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node, const std::string & topic_name,
  const size_t qos_history_depth,
  std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
{
  const agnocast::SubscriptionOptions options;
  return std::make_shared<Subscription<MessageT>>(
    node, topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node, const std::string & topic_name,
  const rclcpp::QoS & qos, std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback,
  agnocast::SubscriptionOptions options)
{
  return std::make_shared<Subscription<MessageT>>(node, topic_name, qos, callback, options);
}

template <typename MessageT>
typename Subscription<MessageT>::SharedPtr create_subscription(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node, const std::string & topic_name,
  const size_t qos_history_depth,
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

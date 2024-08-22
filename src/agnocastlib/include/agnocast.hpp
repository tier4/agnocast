#pragma once

#include "agnocast_publisher.hpp"
#include "agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstring>
#include <functional>
#include <memory>

namespace agnocast
{

void * initialize_agnocast();
size_t read_mq_msgmax();

template <typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(
  std::string topic_name, const rclcpp::QoS & qos)
{
  if (qos.depth() > read_mq_msgmax()) {
    std::cerr << "[Warning]: Publisher may be blocked because the QoS depth is larger than the "
                 "maximum size of POSIX message queue; "
                 "consider reducing the QoS depth or increasing /proc/sys/fs/mqueue/msg_max value."
              << std::endl;
  }
  return std::make_shared<Publisher<MessageT>>(topic_name, qos);
}

template <typename MessageT>
std::shared_ptr<Publisher<MessageT>> create_publisher(
  std::string topic_name, size_t qos_history_depth)
{
  if (qos_history_depth > read_mq_msgmax()) {
    std::cerr << "[Warning]: Publisher may be blocked because the QoS depth is larger than the "
                 "maximum size of POSIX message queue; "
                 "consider reducing the QoS depth or increasing /proc/sys/fs/mqueue/msg_max value."
              << std::endl;
  }
  return std::make_shared<Publisher<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)));
}

template <typename MessageT>
std::shared_ptr<CallbackSubscription<MessageT>> create_subscription(
  const char * topic_name, const rclcpp::QoS & qos,
  std::function<void(const agnocast::message_ptr<MessageT> &)> callback)
{
  return std::make_shared<CallbackSubscription<MessageT>>(topic_name, qos, callback);
}

template <typename MessageT>
std::shared_ptr<CallbackSubscription<MessageT>> create_subscription(
  const char * topic_name, size_t qos_history_depth,
  std::function<void(const agnocast::message_ptr<MessageT> &)> callback)
{
  return std::make_shared<CallbackSubscription<MessageT>>(
    topic_name, rclcpp::QoS(rclcpp::KeepLast(qos_history_depth)), callback);
}

}  // namespace agnocast

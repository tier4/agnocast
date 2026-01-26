// Copyright 2025 The Autoware Contributors
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "agnocast/agnocast.hpp"
#include "agnocast/message_filters/simple_filter.hpp"

#include <rclcpp/rclcpp.hpp>

#include <string>

namespace agnocast
{
namespace message_filters
{

template <class M>
class Subscriber : public SimpleFilter<M>
{
public:
  using MConstPtr = ipc_shared_ptr<const M>;
  using NodePtr = std::shared_ptr<rclcpp::Node>;

  Subscriber(
    rclcpp::Node * node, const std::string & topic, const rclcpp::QoS & qos,
    agnocast::SubscriptionOptions options = agnocast::SubscriptionOptions{})
  {
    subscribe(node, topic, qos, options);
  }

  Subscriber(
    NodePtr node, const std::string & topic, const rclcpp::QoS & qos,
    agnocast::SubscriptionOptions options = agnocast::SubscriptionOptions{})
  {
    subscribe(node.get(), topic, qos, options);
  }

  Subscriber() = default;

  void subscribe(
    rclcpp::Node * node, const std::string & topic, const rclcpp::QoS & qos,
    agnocast::SubscriptionOptions options = agnocast::SubscriptionOptions{})
  {
    unsubscribe();
    node_ = node;
    topic_ = topic;
    qos_ = qos;
    options_ = options;
    subscribe();
  }

  void subscribe(
    NodePtr node, const std::string & topic, const rclcpp::QoS & qos,
    agnocast::SubscriptionOptions options = agnocast::SubscriptionOptions{})
  {
    subscribe(node.get(), topic, qos, options);
  }

  void subscribe()
  {
    if (!node_) {
      return;
    }
    sub_ = agnocast::create_subscription<M>(
      node_, topic_, qos_,
      [this](ipc_shared_ptr<M> msg) { this->signalMessage(std::move(msg)); }, options_);
  }

  void unsubscribe() { sub_.reset(); }

  std::string getTopic() const { return sub_ ? sub_->get_topic_name() : std::string(); }

  const typename agnocast::Subscription<M>::SharedPtr getSubscriber() const { return sub_; }

private:
  typename agnocast::Subscription<M>::SharedPtr sub_;
  rclcpp::Node * node_{nullptr};
  std::string topic_;
  rclcpp::QoS qos_{10};
  agnocast::SubscriptionOptions options_;
};

}  // namespace message_filters
}  // namespace agnocast

#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "rclcpp/rclcpp.hpp"

#include <cstdint>
#include <memory>
#include <regex>

namespace agnocast
{

struct BridgeArgs
{
  char topic_name[256];
  int32_t qos_history;
  int32_t qos_depth;
  int32_t qos_reliability;
};

struct BridgeComponents
{
  rclcpp::Node::SharedPtr node;
  rclcpp::SubscriptionBase::SharedPtr sub;
};

inline std::string generate_node_name(const std::string & topic_name)
{
  constexpr const char * prefix = "agnocast_bridge";
  return prefix + std::regex_replace(topic_name, std::regex("/"), "_");
}

template <typename MessageT>
BridgeComponents start_bridge_node(
  const BridgeArgs & args, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> executor)
{
  std::string topic_name(args.topic_name);

  rclcpp::QoS qos(
    rclcpp::QoSInitialization::from_rmw(
      {static_cast<rmw_qos_history_policy_t>(args.qos_history),
       static_cast<size_t>(args.qos_depth),
       static_cast<rmw_qos_reliability_policy_t>(args.qos_reliability),
       RMW_QOS_POLICY_DURABILITY_VOLATILE,
       {}}));

  auto node_name = agnocast::generate_node_name(topic_name);

  auto node = std::make_shared<rclcpp::Node>(node_name);

  agnocast::PublisherOptions pub_options;
  auto agnocast_pub =
    std::make_shared<agnocast::Publisher<MessageT>>(node.get(), topic_name, qos, pub_options);
  auto callback = [agnocast_pub](const typename MessageT::ConstSharedPtr msg) {
    auto loaned_msg = agnocast_pub->borrow_loaned_message();
    *loaned_msg = *msg;
    agnocast_pub->publish(std::move(loaned_msg));
  };

  rclcpp::SubscriptionOptions sub_options;
  sub_options.ignore_local_publications = true;
  auto sub = node->create_subscription<MessageT>(topic_name, qos, callback, sub_options);

  executor->add_node(node);

  return {node, sub};
}

template <typename MessageT>
BridgeComponents bridge_entry(
  const BridgeArgs & args, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> executor)
{
  return start_bridge_node<MessageT>(args, executor);
}

}  // namespace agnocast

using BridgeFn = agnocast::BridgeComponents (*)(
  const agnocast::BridgeArgs &, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor>);

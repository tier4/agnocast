#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "rclcpp/rclcpp.hpp"

#include <cstdint>
#include <regex>

struct BridgeArgs
{
  char topic_name[256];

  int32_t qos_history;
  int32_t qos_depth;
  int32_t qos_reliability;
};

using BridgeFn =
  void (*)(const BridgeArgs &, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor>);

namespace agnocast
{

struct BridgeComponents
{
  rclcpp::Node::SharedPtr node;
  rclcpp::SubscriptionBase::SharedPtr sub;
};

extern std::map<std::string, BridgeComponents> g_active_bridges;
extern std::mutex g_bridges_mutex;

template <typename MessageT>
void bridge_entry(
  const BridgeArgs & args, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor>);

template <typename MessageT>
void start_bridge_node(
  const BridgeArgs & args, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> executor)
{
  try {
    std::cout << "[Debug] Entering start_bridge_node..." << std::endl;

    std::string topic_name(args.topic_name);

    rclcpp::QoS qos(
      rclcpp::QoSInitialization::from_rmw(
        {static_cast<rmw_qos_history_policy_t>(args.qos_history),
         static_cast<size_t>(args.qos_depth),
         static_cast<rmw_qos_reliability_policy_t>(args.qos_reliability),
         RMW_QOS_POLICY_DURABILITY_VOLATILE,
         {}}));

    auto node_name = "agnocast_bridge" + std::regex_replace(topic_name, std::regex("/"), "_");

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

    {
      std::lock_guard<std::mutex> lock(g_bridges_mutex);
      g_active_bridges[topic_name] = {node, sub};
    }
    executor->add_node(node);

    std::cout << "[Bridge Daemon] Successfully started bridge" << std::endl;

  } catch (const std::exception & e) {
    std::cerr << "[Bridge Daemon CRITICAL ERROR] An exception occurred in start_bridge_node: "
              << e.what() << std::endl;
  } catch (...) {
    std::cerr
      << "[Bridge Daemon CRITICAL ERROR] An unknown exception occurred in start_bridge_node."
      << std::endl;
  }
}

template <typename MessageT>
void bridge_entry(
  const BridgeArgs & args, std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> executor)
{
  start_bridge_node<MessageT>(args, executor);
}

}  // namespace agnocast

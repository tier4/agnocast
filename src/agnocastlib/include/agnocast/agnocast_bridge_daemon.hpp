#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "rclcpp/rclcpp.hpp"

#include <linux/limits.h>  // PATH_MAX を使うために追加
#include <mqueue.h>

#include <cstdint>
#include <regex>

namespace agnocast
{

struct BridgeComponents
{
  rclcpp::Node::SharedPtr node;
  rclcpp::SubscriptionBase::SharedPtr sub;
};

extern std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> g_executor;
extern std::map<std::string, BridgeComponents> g_active_bridges;
extern std::mutex g_bridges_mutex;

struct QoSFlat
{
  uint32_t depth;
  uint8_t history;
  uint8_t reliability;
  uint8_t durability;
};

struct BridgeArgs
{
  char topic_name[256];
  QoSFlat qos;
};

struct ControlMsg
{
  enum Opcode : uint32_t {
    StartBridge = 1,
    Shutdown = 2,
  };

  uint32_t opcode;
  char library_name[PATH_MAX];
  uintptr_t function_offset;
  BridgeArgs args;
};

using BridgeFn = void (*)(const BridgeArgs &);

void bridge_daemon_main(mqd_t mq_read);

inline rclcpp::QoS reconstruct_qos(const QoSFlat & q)
{
  rclcpp::QoS qos(q.depth);
  if (q.history == 1) {
    qos.keep_all();
  }
  if (q.reliability == 1) {
    qos.reliable();
  } else if (q.reliability == 2) {
    qos.best_effort();
  }
  if (q.durability == 1) {
    qos.transient_local();
  }
  return qos;
}

template <typename MessageT>
void bridge_entry(const BridgeArgs & args);

template <typename MessageT>
void start_bridge_node(const BridgeArgs & args)
{
  try {
    std::cout << "[Debug] Entering start_bridge_node..." << std::endl;

    std::string topic_name(args.topic_name);
    rclcpp::QoS qos = reconstruct_qos(args.qos);
    auto node_name = "agnocast_bridge" + std::regex_replace(topic_name, std::regex("/"), "_");

    std::cout << "[Debug] 1. Creating Node..." << std::endl;
    auto node = std::make_shared<rclcpp::Node>(node_name);

    std::cout << "[Debug] 2. Creating Agnocast Publisher..." << std::endl;
    agnocast::PublisherOptions pub_options;
    auto agnocast_pub =
      std::make_shared<agnocast::Publisher<MessageT>>(node.get(), topic_name, qos, pub_options);

    std::cout << "[Debug] 3. Creating ROS 2 Subscription..." << std::endl;
    auto callback = [agnocast_pub, node](const typename MessageT::ConstSharedPtr msg) {
      RCLCPP_INFO(node->get_logger(), "[Bridge Daemon Callback] Message Received!");

      auto loaned_msg = agnocast_pub->borrow_loaned_message();
      RCLCPP_INFO(node->get_logger(), "Address of msg: %p", (void *)msg.get());
      RCLCPP_INFO(
        node->get_logger(), "Address of loaned_msg before copy: %p", (void *)loaned_msg.get());
      *loaned_msg = *msg;
      RCLCPP_INFO(
        node->get_logger(), "Address of loaned_msg after copy: %p", (void *)loaned_msg.get());
      agnocast_pub->publish(std::move(loaned_msg));
    };
    auto sub = node->create_subscription<MessageT>(topic_name, qos, callback);

    {
      std::lock_guard<std::mutex> lock(g_bridges_mutex);
      g_active_bridges[topic_name] = {node, sub};
    }

    std::cout << "[Debug] 4. Adding node to executor..." << std::endl;
    g_executor->add_node(node);

    std::cout << "[Bridge Daemon] Successfully started bridge for topic: " << topic_name
              << std::endl;

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
void bridge_entry(const BridgeArgs & args)
{
  start_bridge_node<MessageT>(args);
}

}  // namespace agnocast
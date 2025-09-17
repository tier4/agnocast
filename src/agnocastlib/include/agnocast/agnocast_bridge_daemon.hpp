#pragma once

#include "agnocast/agnocast_publisher.hpp"

#include <regex>

namespace agnocast
{

extern std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> g_executor;

void bridge_process_main(const MqMsgBridge & msg);

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

    auto sub_holder = std::make_shared<std::shared_ptr<rclcpp::Subscription<MessageT>>>();

    std::cout << "[Debug] 3. Creating ROS 2 Subscription..." << std::endl;

    auto callback = [agnocast_pub, node, sub_holder](const typename MessageT::ConstSharedPtr msg) {
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

    *sub_holder = node->create_subscription<MessageT>(topic_name, qos, callback);

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

using BridgeFn = void (*)(const agnocast::BridgeArgs &);
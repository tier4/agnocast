// bridge_plugin_api.hpp
#pragma once
#include "rclcpp/rclcpp.hpp"

extern "C" rclcpp::SubscriptionBase::SharedPtr create_bridge(
  rclcpp::Node::SharedPtr node, const std::string & topic_name, const rclcpp::QoS & qos);

using CreateBridgeFunc = decltype(&create_bridge);
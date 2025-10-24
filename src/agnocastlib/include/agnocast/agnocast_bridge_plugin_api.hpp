// bridge_plugin_api.hpp
#pragma once
#include "rclcpp/rclcpp.hpp"

extern "C" rclcpp::SubscriptionBase::SharedPtr create_r2a_bridge(
  rclcpp::Node::SharedPtr node, const std::string & topic_name, const rclcpp::QoS & qos);

using CreateR2ABridgeFunc = decltype(&create_r2a_bridge);
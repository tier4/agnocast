#pragma once

#include "rclcpp/clock.hpp"
#include "rclcpp/node_interfaces/node_topics_interface.hpp"
#include "rclcpp/qos.hpp"
#include "rclcpp/subscription.hpp"

#include "rosgraph_msgs/msg/clock.hpp"

#include <rcl/time.h>

#include <memory>

namespace agnocast::node_interfaces
{

class NodeTimeSource
{
public:
  using SharedPtr = std::shared_ptr<NodeTimeSource>;

  NodeTimeSource(
    rclcpp::Clock::SharedPtr clock,
    rclcpp::node_interfaces::NodeTopicsInterface::SharedPtr node_topics,
    const rclcpp::QoS & qos = rclcpp::ClockQoS());

  ~NodeTimeSource();

  NodeTimeSource(const NodeTimeSource &) = delete;
  NodeTimeSource & operator=(const NodeTimeSource &) = delete;

  void enable_ros_time();

private:
  void create_clock_subscription();
  void clock_callback(std::shared_ptr<const rosgraph_msgs::msg::Clock> msg);

  rclcpp::Clock::SharedPtr clock_;
  rclcpp::node_interfaces::NodeTopicsInterface::SharedPtr node_topics_;
  rclcpp::QoS qos_;
  rclcpp::Subscription<rosgraph_msgs::msg::Clock>::SharedPtr clock_subscription_;
};

}  // namespace agnocast::node_interfaces

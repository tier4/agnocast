#pragma once

#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/clock.hpp"
#include "rclcpp/node_interfaces/node_time_source_interface.hpp"
#include "rclcpp/qos.hpp"

#include "rosgraph_msgs/msg/clock.hpp"

#include <rcl/time.h>

#include <memory>

namespace agnocast
{
class Node;
}

namespace agnocast::node_interfaces
{

class NodeTimeSource : public rclcpp::node_interfaces::NodeTimeSourceInterface
{
public:
  RCLCPP_SMART_PTR_ALIASES_ONLY(NodeTimeSource)

  NodeTimeSource(
    agnocast::Node * node, rclcpp::Clock::SharedPtr clock,
    const rclcpp::QoS & qos = rclcpp::ClockQoS());

  ~NodeTimeSource() override;

  NodeTimeSource(const NodeTimeSource &) = delete;
  NodeTimeSource & operator=(const NodeTimeSource &) = delete;

  void enable_ros_time();

private:
  void create_clock_subscription();
  void clock_callback(agnocast::ipc_shared_ptr<const rosgraph_msgs::msg::Clock> msg);

  agnocast::Node * node_;
  rclcpp::Clock::SharedPtr clock_;
  rclcpp::QoS qos_;
  agnocast::Subscription<rosgraph_msgs::msg::Clock>::SharedPtr clock_subscription_;
};

}  // namespace agnocast::node_interfaces

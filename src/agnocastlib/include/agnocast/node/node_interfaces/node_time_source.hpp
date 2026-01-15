#pragma once

#include "agnocast/agnocast_subscription.hpp"
#include "builtin_interfaces/msg/time.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_clock_interface.hpp"
#include "rclcpp/node_interfaces/node_parameters_interface.hpp"
#include "rclcpp/node_interfaces/node_time_source_interface.hpp"
#include "rclcpp/qos.hpp"

#include "rosgraph_msgs/msg/clock.hpp"

namespace agnocast
{
class Node;
}

namespace agnocast::node_interfaces
{

class NodeTimeSource : public rclcpp::node_interfaces::NodeTimeSourceInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTimeSource>;
  using WeakPtr = std::weak_ptr<NodeTimeSource>;

  NodeTimeSource(
    rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock, agnocast::Node * node,
    const rclcpp::QoS & qos = rclcpp::ClockQoS());

  ~NodeTimeSource() override;

private:
  // Preserve the node reference
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_;

  // Agnocast node for creating subscriptions
  agnocast::Node * agnocast_node_{nullptr};

  // QoS of the clock subscription
  rclcpp::QoS qos_;

  // The subscription for the clock callback
  agnocast::Subscription<rosgraph_msgs::msg::Clock>::SharedPtr clock_subscription_;

  // Attached clock (single clock for minimal version)
  rclcpp::Clock::SharedPtr clock_;

  // Whether ros time is active
  bool ros_time_active_{false};

  // An internal method to use in the clock callback that enables ros time
  void enable_ros_time();

  // An internal method to use in the clock callback that disables ros time
  void disable_ros_time();

  // Internal helper function for setting clock time
  void set_clock(const builtin_interfaces::msg::Time & msg, bool set_ros_time_enabled);

  // Create the subscription for the clock topic
  void create_clock_sub();

  // Destroy the subscription for the clock topic
  void destroy_clock_sub();

  // The clock callback itself
  void clock_cb(const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg);

  // Attach/detach methods
  void attachNode(agnocast::Node * node);
  void detachNode();
  void attachClock(rclcpp::Clock::SharedPtr clock);
};

}  // namespace agnocast::node_interfaces

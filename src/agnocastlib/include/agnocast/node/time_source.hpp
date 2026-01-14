#pragma once

#include "rclcpp/clock.hpp"
#include "rclcpp/macros.hpp"
#include "rclcpp/qos.hpp"

#include <memory>

namespace agnocast
{
class Node;

class TimeSource
{
public:
  explicit TimeSource(agnocast::Node * node, const rclcpp::QoS & qos = rclcpp::ClockQoS());

  explicit TimeSource(const rclcpp::QoS & qos = rclcpp::ClockQoS());

  TimeSource(const TimeSource &) = delete;
  TimeSource & operator=(const TimeSource &) = delete;

  TimeSource(TimeSource &&) = default;
  TimeSource & operator=(TimeSource &&) = default;

  void attachNode(agnocast::Node * node);

  void detachNode();

  void attachClock(rclcpp::Clock::SharedPtr clock);

  void detachClock(rclcpp::Clock::SharedPtr clock);

  ~TimeSource();

private:
  class NodeState;
  std::shared_ptr<NodeState> node_state_;

  rclcpp::QoS constructed_qos_;
};

}  // namespace agnocast

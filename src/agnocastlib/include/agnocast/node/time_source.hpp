#pragma once

#include "rclcpp/clock.hpp"
#include "rclcpp/macros.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_parameters_interface.hpp"
#include "rclcpp/qos.hpp"

#include <memory>

namespace agnocast
{
class Node;

/**
 * Time source that will drive the attached clock.
 *
 * If the attached node `use_sim_time` parameter is `true`, the attached clock will
 * be updated based on messages received on the `/clock` topic.
 */
class TimeSource
{
public:
  /// Constructor
  /**
   * The node will be attached to the time source.
   *
   * \param node raw pointer to a initialized agnocast node
   * \param qos QoS that will be used when creating a `/clock` subscription.
   */
  explicit TimeSource(agnocast::Node * node, const rclcpp::QoS & qos = rclcpp::ClockQoS());

  /// Empty constructor
  /**
   * An Empty TimeSource class
   *
   * \param qos QoS that will be used when creating a `/clock` subscription.
   */
  explicit TimeSource(const rclcpp::QoS & qos = rclcpp::ClockQoS());

  // The TimeSource is uncopyable
  TimeSource(const TimeSource &) = delete;
  TimeSource & operator=(const TimeSource &) = delete;

  // The TimeSource is moveable
  TimeSource(TimeSource &&) = default;
  TimeSource & operator=(TimeSource &&) = default;

  /// Attach node to the time source.
  /**
   * \param node raw pointer to a initialized agnocast node
   */
  void attachNode(agnocast::Node * node);

  /// Attach node to the time source.
  /**
   * If the parameter `use_sim_time` is `true` then the source time is the simulation time,
   * otherwise the source time is defined by the system.
   *
   * \param node_base_interface Node base interface.
   * \param node_parameters_interface Node parameters interface.
   * \param node Agnocast node for creating subscriptions.
   */
  void attachNode(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_interface,
    rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_interface,
    agnocast::Node * node);

  /// Detach the node from the time source
  void detachNode();

  /// Attach a clock to the time source to be updated
  /**
   * \param[in] clock to attach to the time source
   * \throws std::invalid_argument the time source must be a RCL_ROS_TIME otherwise throws an
   * exception
   */
  void attachClock(rclcpp::Clock::SharedPtr clock);

  /// Detach a clock from the time source
  void detachClock(rclcpp::Clock::SharedPtr clock);

  /// TimeSource Destructor
  ~TimeSource();

private:
  class NodeState;
  std::shared_ptr<NodeState> node_state_;

  // Preserve the arguments received by the constructor for reuse at runtime
  rclcpp::QoS constructed_qos_;
};

}  // namespace agnocast

#ifndef AGNOCAST__NODE__NODE_INTERFACES__NODE_TIMERS_HPP_
#define AGNOCAST__NODE__NODE_INTERFACES__NODE_TIMERS_HPP_

#include "agnocast/node/node_interfaces/node_base.hpp"
#include "rclcpp/callback_group.hpp"
#include "rclcpp/node_interfaces/node_timers_interface.hpp"
#include "rclcpp/timer.hpp"

#include <memory>

namespace agnocast::node_interfaces
{

/// \brief Implementation of NodeTimersInterface for Agnocast.
///
/// This class provides timer management for agnocast::Node, implementing the
/// rclcpp::node_interfaces::NodeTimersInterface to allow compatibility with
/// libraries that expect this interface (e.g., tf2_ros::CreateTimerROS).
///
/// Timers added through this interface are executed by the executor's
/// ros2_spin() thread, not by agnocast's internal timer mechanism.
class NodeTimers : public rclcpp::node_interfaces::NodeTimersInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTimers>;

  /// \brief Constructor
  /// \param node_base Pointer to the node's base interface
  explicit NodeTimers(NodeBase * node_base);

  virtual ~NodeTimers() = default;

  /// \brief Add a timer to the node.
  ///
  /// The timer will be added to the specified callback group (or the default
  /// callback group if none is specified). The timer will be executed by the
  /// executor when it fires.
  ///
  /// \param timer The timer to add
  /// \param callback_group The callback group to add the timer to (optional)
  void add_timer(
    rclcpp::TimerBase::SharedPtr timer, rclcpp::CallbackGroup::SharedPtr callback_group) override;

private:
  NodeBase * node_base_;
};

}  // namespace agnocast::node_interfaces

#endif  // AGNOCAST__NODE__NODE_INTERFACES__NODE_TIMERS_HPP_

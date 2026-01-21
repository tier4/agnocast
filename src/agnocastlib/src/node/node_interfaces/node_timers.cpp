#include "agnocast/node/node_interfaces/node_timers.hpp"

#include "rclcpp/logging.hpp"

#include <stdexcept>

namespace agnocast::node_interfaces
{

NodeTimers::NodeTimers(NodeBase * node_base) : node_base_(node_base)
{
}

void NodeTimers::add_timer(
  rclcpp::TimerBase::SharedPtr /*timer*/, rclcpp::CallbackGroup::SharedPtr /*callback_group*/)
{
  // TODO(agnocast): rclcpp::TimerBase is not supported in agnocast because:
  // 1. rclcpp::Timer requires DDS infrastructure (rcl_timer, rcl_wait)
  // 2. agnocast uses timerfd + epoll for timers to avoid DDS participation
  //
  // For tf2 timer functionality, use agnocast::CreateTimerAgnocast which implements
  // tf2_ros::CreateTimerInterface using agnocast's native timer mechanism.
  //
  // Example:
  //   auto timer_interface = std::make_shared<agnocast::CreateTimerAgnocast>();
  //   buffer.setCreateTimerInterface(timer_interface);
  throw std::runtime_error(
    "NodeTimers::add_timer is not supported in agnocast. "
    "rclcpp::Timer requires DDS infrastructure. "
    "For tf2 timers, use agnocast::CreateTimerAgnocast instead.");
}

}  // namespace agnocast::node_interfaces

#include "agnocast/node/node_interfaces/node_time_source.hpp"

#include "agnocast/node/agnocast_node.hpp"
#include "rclcpp/logging.hpp"
#include "rclcpp/time.hpp"

namespace agnocast::node_interfaces
{

NodeTimeSource::NodeTimeSource(
  agnocast::Node * node, rclcpp::Clock::SharedPtr clock, const rclcpp::QoS & qos)
: node_(node), clock_(clock), qos_(qos)
{
  // TODO(Koichi98): Subscribe to /parameter_events using
  // rclcpp::AsyncParametersClient::on_parameter_event() for dynamic use_sim_time changes
}

NodeTimeSource::~NodeTimeSource()
{
  if (clock_ && clock_->get_clock_type() == RCL_ROS_TIME) {
    rcl_clock_t * rcl_clock = clock_->get_clock_handle();
    [[maybe_unused]] rcl_ret_t ret = rcl_disable_ros_time_override(rcl_clock);
  }
}

void NodeTimeSource::enable_ros_time()
{
  if (clock_->get_clock_type() != RCL_ROS_TIME) {
    RCLCPP_WARN(
      rclcpp::get_logger("agnocast"), "use_sim_time is true but clock type is not RCL_ROS_TIME");
    return;
  }

  rcl_clock_t * rcl_clock = clock_->get_clock_handle();
  rcl_ret_t ret = rcl_enable_ros_time_override(rcl_clock);
  if (ret != RCL_RET_OK) {
    RCLCPP_ERROR(rclcpp::get_logger("agnocast"), "Failed to enable ROS time override");
    return;
  }

  create_clock_subscription();
}

void NodeTimeSource::create_clock_subscription()
{
  clock_subscription_ = node_->create_subscription<rosgraph_msgs::msg::Clock>(
    "/clock", qos_,
    [this](agnocast::ipc_shared_ptr<const rosgraph_msgs::msg::Clock> msg) { clock_callback(msg); });
}

void NodeTimeSource::clock_callback(agnocast::ipc_shared_ptr<const rosgraph_msgs::msg::Clock> msg)
{
  rcl_clock_t * rcl_clock = clock_->get_clock_handle();
  rcl_ret_t ret = rcl_set_ros_time_override(rcl_clock, rclcpp::Time(msg->clock).nanoseconds());
  if (ret != RCL_RET_OK) {
    RCLCPP_ERROR(rclcpp::get_logger("agnocast"), "Failed to set ROS time override");
  }
}

}  // namespace agnocast::node_interfaces

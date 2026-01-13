#include "agnocast/node/node_interfaces/node_time_source.hpp"

#include "rclcpp/create_subscription.hpp"
#include "rclcpp/logging.hpp"
#include "rclcpp/time.hpp"

namespace agnocast::node_interfaces
{

NodeTimeSource::NodeTimeSource(
  rclcpp::Clock::SharedPtr clock, bool use_sim_time,
  rclcpp::node_interfaces::NodeTopicsInterface::SharedPtr node_topics, const rclcpp::QoS & qos)
: clock_(clock)
{
  // TODO(Koichi98): Subscribe to /parameter_events using
  // rclcpp::AsyncParametersClient::on_parameter_event() for dynamic use_sim_time changes

  if (!use_sim_time) {
    return;
  }

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

  clock_subscription_ = rclcpp::create_subscription<rosgraph_msgs::msg::Clock>(
    node_topics, "/clock", qos,
    [this](std::shared_ptr<const rosgraph_msgs::msg::Clock> msg) { clock_callback(msg); });
}

NodeTimeSource::~NodeTimeSource()
{
  if (clock_ && clock_->get_clock_type() == RCL_ROS_TIME) {
    rcl_clock_t * rcl_clock = clock_->get_clock_handle();
    [[maybe_unused]] rcl_ret_t ret = rcl_disable_ros_time_override(rcl_clock);
  }
}

void NodeTimeSource::clock_callback(std::shared_ptr<const rosgraph_msgs::msg::Clock> msg)
{
  rcl_clock_t * rcl_clock = clock_->get_clock_handle();
  rcl_ret_t ret = rcl_set_ros_time_override(rcl_clock, rclcpp::Time(msg->clock).nanoseconds());
  if (ret != RCL_RET_OK) {
    RCLCPP_ERROR(rclcpp::get_logger("agnocast"), "Failed to set ROS time override");
  }
}

}  // namespace agnocast::node_interfaces

#include "agnocast/node/time_source.hpp"

#include "agnocast/bridge/agnocast_bridge_node.hpp"
#include "agnocast/node/agnocast_node.hpp"
#include "rcl/time.h"
#include "rclcpp/parameter_client.hpp"

#include "rosgraph_msgs/msg/clock.hpp"

#include <memory>
#include <string>
#include <utility>

namespace agnocast
{

const std::string use_sim_time_name = "use_sim_time";

// TODO(Koichi98): Add ClocksState class for multiple clock support
// class ClocksState final
// {
// public:
//   void enable_ros_time();
//   void disable_ros_time();
//   bool is_ros_time_active() const;
//   void attachClock(rclcpp::Clock::SharedPtr clock);
//   void detachClock(rclcpp::Clock::SharedPtr clock);
//   static void set_clock(const builtin_interfaces::msg::Time::SharedPtr msg,
//                         bool set_ros_time_enabled, rclcpp::Clock::SharedPtr clock);
//   void set_all_clocks(const builtin_interfaces::msg::Time::SharedPtr msg, bool
//   set_ros_time_enabled); void cache_last_msg(std::shared_ptr<const rosgraph_msgs::msg::Clock>
//   msg);
// private:
//   std::mutex clock_list_lock_;
//   std::vector<rclcpp::Clock::SharedPtr> associated_clocks_;
//   bool ros_time_active_{false};
//   std::shared_ptr<const rosgraph_msgs::msg::Clock> last_msg_set_;
// };

class TimeSource::NodeState final
{
public:
  explicit NodeState(const rclcpp::QoS & qos);
  ~NodeState();

  // Attach a node to this time source
  void attachNode(agnocast::Node * node);

  // Detach the attached node
  void detachNode();

  void attachClock(rclcpp::Clock::SharedPtr clock);

  void detachClock(rclcpp::Clock::SharedPtr clock);

private:
  // TODO(Koichi98): Replace with ClocksState for multiple clock support
  // ClocksState clocks_state_;

  // TODO(Koichi98): Add dedicated thread for clock subscription
  // bool use_clock_thread_;
  // std::thread clock_executor_thread_;

  // Preserve the node reference
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  // TODO(Koichi98): Add node_topics_, node_graph_, node_services_, node_logging_, node_clock_
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_;

  // Agnocast node for creating subscriptions
  agnocast::Node * agnocast_node_{nullptr};

  // QoS of the clock subscription
  rclcpp::QoS qos_;

  // The subscription for the clock callback
  agnocast::Subscription<rosgraph_msgs::msg::Clock>::SharedPtr clock_subscription_;
  // TODO(Koichi98): Add clock_sub_lock_, clock_callback_group_, clock_executor_

  // TODO(Koichi98): Replace with ClocksState for multiple clock support
  // Attached clock (single clock for minimal version)
  rclcpp::Clock::SharedPtr clock_;

  // Whether ros time is active
  bool ros_time_active_{false};

  // TODO(Koichi98): Add parameter_subscription_ for runtime parameter changes
  // using ParamSubscriptionT = rclcpp::Subscription<rcl_interfaces::msg::ParameterEvent>;
  // std::shared_ptr<ParamSubscriptionT> parameter_subscription_;

  // An internal method to use in the clock callback that enables ros time
  void enable_ros_time();

  // An internal method to use in the clock callback that disables ros time
  void disable_ros_time();

  // Internal helper function used inside iterators
  // Note: In rclcpp, this is ClocksState::set_clock() which handles both
  // enabling/disabling ros time override and setting the time value.
  void set_clock(const builtin_interfaces::msg::Time & msg, bool set_ros_time_enabled);

  // Create the subscription for the clock topic
  void create_clock_sub();

  // Destroy the subscription for the clock topic
  void destroy_clock_sub();

  // The clock callback itself
  void clock_cb(const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg);
};

TimeSource::NodeState::NodeState(const rclcpp::QoS & qos) : qos_(qos)
{
}

TimeSource::NodeState::~NodeState()
{
  if (node_base_ || node_parameters_) {
    detachNode();
  }
}

void TimeSource::NodeState::attachNode(agnocast::Node * node)
{
  node_base_ = node->get_node_base_interface();
  node_parameters_ = node->get_node_parameters_interface();
  agnocast_node_ = node;

  // Though this defaults to false, it can be overridden by initial parameter values for the
  // node, which may be given by the user at the node's construction or even by command-line
  // arguments.
  rclcpp::ParameterValue use_sim_time_param;
  if (!node_parameters_->has_parameter(use_sim_time_name)) {
    use_sim_time_param =
      node_parameters_->declare_parameter(use_sim_time_name, rclcpp::ParameterValue(false));
  } else {
    use_sim_time_param = node_parameters_->get_parameter(use_sim_time_name).get_parameter_value();
  }
  if (use_sim_time_param.get_type() == rclcpp::PARAMETER_BOOL) {
    if (use_sim_time_param.get<bool>()) {
      enable_ros_time();
      create_clock_sub();
    }
  } else {
    throw std::invalid_argument("Invalid type for parameter 'use_sim_time', should be 'bool'");
  }

  // TODO(Koichi98): Add parameter event subscription using
  // rclcpp::AsyncParametersClient::on_parameter_event
}

void TimeSource::NodeState::detachNode()
{
  // destroy_clock_sub() *must* be first here, to ensure that the executor
  // can't possibly call any of the callbacks as we are cleaning up.
  destroy_clock_sub();
  disable_ros_time();
  // TODO(Koichi98): Add parameter_subscription_.reset()
  node_base_.reset();
  node_parameters_.reset();
  agnocast_node_ = nullptr;
}

void TimeSource::NodeState::attachClock(rclcpp::Clock::SharedPtr clock)
{
  if (clock->get_clock_type() != RCL_ROS_TIME) {
    throw std::invalid_argument("Cannot attach a clock that is not ROS_TIME");
  }

  // TODO(Koichi98): Use ClocksState to manage multiple clocks
  clock_ = std::move(clock);

  if (ros_time_active_) {
    enable_ros_time();
    // TODO(Koichi98): Send cached last message to newly attached clock
  }
}

void TimeSource::NodeState::detachClock(rclcpp::Clock::SharedPtr clock)
{
  if (clock_ == clock) {
    disable_ros_time();
    clock_.reset();
  }
}

void TimeSource::NodeState::enable_ros_time()
{
  if (ros_time_active_) {
    // already enabled no-op
    return;
  }

  // Local storage
  ros_time_active_ = true;

  // Update the attached clock to zero or last recorded time
  // TODO(Koichi98): Use last_msg_set_ for cached time
  builtin_interfaces::msg::Time time_msg;
  set_clock(time_msg, true);
}

void TimeSource::NodeState::disable_ros_time()
{
  if (!ros_time_active_) {
    // already disabled no-op
    return;
  }

  // Local storage
  ros_time_active_ = false;

  // Update the attached clock
  builtin_interfaces::msg::Time time_msg;
  set_clock(time_msg, false);
}

void TimeSource::NodeState::set_clock(
  const builtin_interfaces::msg::Time & msg, bool set_ros_time_enabled)
{
  if (!clock_) {
    return;
  }

  // TODO(Koichi98): Add std::lock_guard<std::mutex> clock_guard(clock->get_clock_mutex())

  // Do change
  if (!set_ros_time_enabled && clock_->ros_time_is_active()) {
    auto ret = rcl_disable_ros_time_override(clock_->get_clock_handle());
    if (ret != RCL_RET_OK) {
      throw std::runtime_error("Failed to disable ros_time_override: " + std::to_string(ret));
    }
  } else if (set_ros_time_enabled && !clock_->ros_time_is_active()) {
    auto ret = rcl_enable_ros_time_override(clock_->get_clock_handle());
    if (ret != RCL_RET_OK) {
      throw std::runtime_error("Failed to enable ros_time_override: " + std::to_string(ret));
    }
  }

  rcl_time_point_value_t time_point =
    static_cast<rcl_time_point_value_t>(RCL_S_TO_NS(msg.sec)) + msg.nanosec;
  auto ret = rcl_set_ros_time_override(clock_->get_clock_handle(), time_point);
  if (ret != RCL_RET_OK) {
    throw std::runtime_error("Failed to set ros_time_override: " + std::to_string(ret));
  }
}

void TimeSource::NodeState::create_clock_sub()
{
  if (clock_subscription_) {
    // Subscription already created.
    return;
  }

  // TODO(Koichi98): Add QoS override support using
  // rclcpp::SubscriptionOptions::qos_overriding_options
  // TODO(Koichi98): Add clock thread support (use_clock_thread_, clock_callback_group_,
  // clock_executor_)

  clock_subscription_ = agnocast_node_->create_subscription<rosgraph_msgs::msg::Clock>(
    "/clock", qos_,
    [this](const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg) { clock_cb(msg); });
}

void TimeSource::NodeState::destroy_clock_sub()
{
  // TODO(Koichi98): Add clock thread cleanup (clock_executor_thread_.join(), etc.)
  clock_subscription_.reset();
}

void TimeSource::NodeState::clock_cb(
  const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg)
{
  if (!ros_time_active_) {
    enable_ros_time();
  }
  // Cache the last message in case a new clock is attached.
  // TODO(Koichi98): last_msg_set_ = msg;

  set_clock(msg->clock, true);
}

// TimeSource implementation

TimeSource::TimeSource(agnocast::Node * node, const rclcpp::QoS & qos) : TimeSource(qos)
{
  attachNode(node);
}

TimeSource::TimeSource(const rclcpp::QoS & qos) : constructed_qos_(qos)
{
  node_state_ = std::make_shared<NodeState>(qos);
}

TimeSource::~TimeSource() = default;

void TimeSource::attachNode(agnocast::Node * node)
{
  node_state_->attachNode(node);
}

void TimeSource::detachNode()
{
  node_state_->detachNode();
}

void TimeSource::attachClock(rclcpp::Clock::SharedPtr clock)
{
  node_state_->attachClock(std::move(clock));
}

void TimeSource::detachClock(rclcpp::Clock::SharedPtr clock)
{
  node_state_->detachClock(std::move(clock));
}

}  // namespace agnocast

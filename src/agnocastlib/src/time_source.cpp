#include "agnocast/time_source.hpp"

#include "agnocast/agnocast_single_threaded_executor.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "agnocast/bridge/agnocast_bridge_node.hpp"
#include "agnocast/node/agnocast_node.hpp"
#include "builtin_interfaces/msg/time.hpp"
#include "rclcpp/exceptions.hpp"
#include "rclcpp/logging.hpp"
#include "rclcpp/time.hpp"

#include "rosgraph_msgs/msg/clock.hpp"

#include <rcl/time.h>

#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <utility>
#include <vector>

namespace agnocast
{

class ClocksState final
{
public:
  ClocksState() : logger_(rclcpp::get_logger("agnocast")) {}

  // An internal method to use in the clock callback that iterates and enables all clocks
  void enable_ros_time()
  {
    if (ros_time_active_) {
      // already enabled no-op
      return;
    }

    // Local storage
    ros_time_active_ = true;

    // Update all attached clocks to zero or last recorded time
    std::lock_guard<std::mutex> guard(clock_list_lock_);
    auto time_msg = std::make_shared<builtin_interfaces::msg::Time>();
    if (last_msg_set_) {
      time_msg = std::make_shared<builtin_interfaces::msg::Time>(last_msg_set_->clock);
    }
    for (auto it = associated_clocks_.begin(); it != associated_clocks_.end(); ++it) {
      set_clock(time_msg, true, *it);
    }
  }

  // An internal method to use in the clock callback that iterates and disables all clocks
  void disable_ros_time()
  {
    if (!ros_time_active_) {
      // already disabled no-op
      return;
    }

    // Local storage
    ros_time_active_ = false;

    // Update all attached clocks
    std::lock_guard<std::mutex> guard(clock_list_lock_);
    for (auto it = associated_clocks_.begin(); it != associated_clocks_.end(); ++it) {
      auto msg = std::make_shared<builtin_interfaces::msg::Time>();
      set_clock(msg, false, *it);
    }
  }

  // Check if ROS time is active
  bool is_ros_time_active() const { return ros_time_active_; }

  // Attach a clock
  void attachClock(rclcpp::Clock::SharedPtr clock)
  {
    if (clock->get_clock_type() != RCL_ROS_TIME) {
      throw std::invalid_argument("Cannot attach clock to a time source that's not a ROS clock");
    }

    std::lock_guard<std::mutex> guard(clock_list_lock_);
    associated_clocks_.push_back(clock);
    // Set the clock to zero unless there's a recently received message
    auto time_msg = std::make_shared<builtin_interfaces::msg::Time>();
    if (last_msg_set_) {
      time_msg = std::make_shared<builtin_interfaces::msg::Time>(last_msg_set_->clock);
    }
    set_clock(time_msg, ros_time_active_, clock);
  }

  // Detach a clock
  void detachClock(rclcpp::Clock::SharedPtr clock)
  {
    std::lock_guard<std::mutex> guard(clock_list_lock_);
    auto result = std::find(associated_clocks_.begin(), associated_clocks_.end(), clock);
    if (result != associated_clocks_.end()) {
      associated_clocks_.erase(result);
    } else {
      RCLCPP_ERROR(logger_, "failed to remove clock");
    }
  }

  // Internal helper function used inside iterators
  static void set_clock(
    const builtin_interfaces::msg::Time::SharedPtr msg, bool set_ros_time_enabled,
    rclcpp::Clock::SharedPtr clock)
  {
    std::lock_guard<std::mutex> clock_guard(clock->get_clock_mutex());

    // Do change
    if (!set_ros_time_enabled && clock->ros_time_is_active()) {
      auto ret = rcl_disable_ros_time_override(clock->get_clock_handle());
      if (ret != RCL_RET_OK) {
        rclcpp::exceptions::throw_from_rcl_error(ret, "Failed to disable ros_time_override_status");
      }
    } else if (set_ros_time_enabled && !clock->ros_time_is_active()) {
      auto ret = rcl_enable_ros_time_override(clock->get_clock_handle());
      if (ret != RCL_RET_OK) {
        rclcpp::exceptions::throw_from_rcl_error(ret, "Failed to enable ros_time_override_status");
      }
    }

    auto ret =
      rcl_set_ros_time_override(clock->get_clock_handle(), rclcpp::Time(*msg).nanoseconds());
    if (ret != RCL_RET_OK) {
      rclcpp::exceptions::throw_from_rcl_error(ret, "Failed to set ros_time_override_status");
    }
  }

  // Internal helper function
  void set_all_clocks(const builtin_interfaces::msg::Time::SharedPtr msg, bool set_ros_time_enabled)
  {
    std::lock_guard<std::mutex> guard(clock_list_lock_);
    for (auto it = associated_clocks_.begin(); it != associated_clocks_.end(); ++it) {
      set_clock(msg, set_ros_time_enabled, *it);
    }
  }

  // Cache the last clock message received
  void cache_last_msg(std::shared_ptr<const rosgraph_msgs::msg::Clock> msg) { last_msg_set_ = msg; }

private:
  // Store (and update on node attach) logger for logging.
  rclcpp::Logger logger_;

  // A lock to protect iterating the associated_clocks_ field.
  std::mutex clock_list_lock_;
  // A vector to store references to associated clocks.
  std::vector<rclcpp::Clock::SharedPtr> associated_clocks_;

  // Local storage of validity of ROS time
  // This is needed when new clocks are added.
  bool ros_time_active_{false};
  // Last set message to be passed to newly registered clocks
  std::shared_ptr<const rosgraph_msgs::msg::Clock> last_msg_set_;
};

class TimeSource::NodeState final
{
public:
  NodeState(const rclcpp::QoS & qos, bool use_clock_thread)
  : use_clock_thread_(use_clock_thread), logger_(rclcpp::get_logger("agnocast")), qos_(qos)
  {
  }

  ~NodeState()
  {
    if (node_base_ || node_parameters_) {
      detachNode();
    }
  }

  // Check if a clock thread will be used
  bool get_use_clock_thread() { return use_clock_thread_; }

  // Set whether a clock thread will be used
  void set_use_clock_thread(bool use_clock_thread) { use_clock_thread_ = use_clock_thread; }

  // Check if the clock thread is joinable
  bool clock_thread_is_joinable() { return clock_executor_thread_.joinable(); }

  // Attach a node to this time source
  void attachNode(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_interface,
    rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_interface,
    rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock_interface,
    agnocast::Node * node)
  {
    node_base_ = node_base_interface;
    node_parameters_ = node_parameters_interface;
    node_clock_ = node_clock_interface;
    node_ = node;

    logger_ = rclcpp::get_logger(node_base_->get_fully_qualified_name());

    // Though this defaults to false, it can be overridden by initial parameter values for the
    // node, which may be given by the user at the node's construction or even by command-line
    // arguments.
    rclcpp::ParameterValue use_sim_time_param;
    const std::string use_sim_time_name = "use_sim_time";
    if (!node_parameters_->has_parameter(use_sim_time_name)) {
      use_sim_time_param =
        node_parameters_->declare_parameter(use_sim_time_name, rclcpp::ParameterValue(false));
    } else {
      use_sim_time_param = node_parameters_->get_parameter(use_sim_time_name).get_parameter_value();
    }
    if (use_sim_time_param.get_type() == rclcpp::PARAMETER_BOOL) {
      if (use_sim_time_param.get<bool>()) {
        parameter_state_ = SET_TRUE;
        clocks_state_.enable_ros_time();
        create_clock_sub();
      }
    } else {
      RCLCPP_ERROR(
        logger_, "Invalid type '%s' for parameter 'use_sim_time', should be 'bool'",
        rclcpp::to_string(use_sim_time_param.get_type()).c_str());
      throw std::invalid_argument("Invalid type for parameter 'use_sim_time', should be 'bool'");
    }

    // NOTE: Dynamic use_sim_time parameter changes via parameter events are not supported.
    // This would require subscribing to /parameter_events using
    // rclcpp::AsyncParametersClient::on_parameter_event().
  }

  // Detach the attached node
  void detachNode()
  {
    // destroy_clock_sub() *must* be first here, to ensure that the executor
    // can't possibly call any of the callbacks as we are cleaning up.
    destroy_clock_sub();
    clocks_state_.disable_ros_time();
    node_base_.reset();
    node_parameters_.reset();
    node_clock_.reset();
    node_ = nullptr;
  }

  void attachClock(std::shared_ptr<rclcpp::Clock> clock)
  {
    clocks_state_.attachClock(std::move(clock));
  }

  void detachClock(std::shared_ptr<rclcpp::Clock> clock)
  {
    clocks_state_.detachClock(std::move(clock));
  }

private:
  ClocksState clocks_state_;

  // Dedicated thread for clock subscription.
  bool use_clock_thread_;
  std::thread clock_executor_thread_;

  // Preserve the node reference
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_{nullptr};
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_{nullptr};
  rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock_{nullptr};
  agnocast::Node * node_{nullptr};

  // Store (and update on node attach) logger for logging.
  rclcpp::Logger logger_;

  // QoS of the clock subscription.
  rclcpp::QoS qos_;

  // The subscription for the clock callback
  agnocast::Subscription<rosgraph_msgs::msg::Clock>::SharedPtr clock_subscription_{nullptr};
  std::mutex clock_sub_lock_;
  rclcpp::CallbackGroup::SharedPtr clock_callback_group_;
  std::shared_ptr<agnocast::SingleThreadedAgnocastExecutor> clock_executor_;
  std::promise<void> cancel_clock_executor_promise_;

  // The clock callback itself
  void clock_cb(const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg)
  {
    if (!clocks_state_.is_ros_time_active() && SET_TRUE == this->parameter_state_) {
      clocks_state_.enable_ros_time();
    }
    // Cache the last message in case a new clock is attached.
    // Convert to std::shared_ptr for caching
    auto msg_copy = std::make_shared<rosgraph_msgs::msg::Clock>(*msg);
    clocks_state_.cache_last_msg(msg_copy);
    auto time_msg = std::make_shared<builtin_interfaces::msg::Time>(msg->clock);

    if (SET_TRUE == this->parameter_state_) {
      clocks_state_.set_all_clocks(time_msg, true);
    }
  }

  // Create the subscription for the clock topic
  void create_clock_sub()
  {
    std::lock_guard<std::mutex> guard(clock_sub_lock_);
    if (clock_subscription_) {
      // Subscription already created.
      return;
    }

    agnocast::SubscriptionOptions options;
    options.qos_overriding_options = rclcpp::QosOverridingOptions(
      {rclcpp::QosPolicyKind::Depth, rclcpp::QosPolicyKind::Durability,
       rclcpp::QosPolicyKind::History, rclcpp::QosPolicyKind::Reliability});

    if (use_clock_thread_) {
      clock_callback_group_ =
        node_base_->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive, false);
      options.callback_group = clock_callback_group_;
      rclcpp::ExecutorOptions exec_options;
      exec_options.context = node_base_->get_context();
      clock_executor_ = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>(exec_options);
      if (!clock_executor_thread_.joinable()) {
        cancel_clock_executor_promise_ = std::promise<void>{};
        clock_executor_thread_ = std::thread([this]() {
          auto future = cancel_clock_executor_promise_.get_future();
          clock_executor_->dedicate_to_callback_group(clock_callback_group_, node_base_);
          clock_executor_->spin_until_future_complete(future);
        });
      }
    }

    clock_subscription_ = node_->create_subscription<rosgraph_msgs::msg::Clock>(
      "/clock", qos_,
      [this](const agnocast::ipc_shared_ptr<rosgraph_msgs::msg::Clock> & msg) {
        // We are using node_base_ as an indication if there is a node attached.
        // Only call the clock_cb if that is the case.
        if (node_base_ != nullptr) {
          clock_cb(msg);
        }
      },
      options);
  }

  // Destroy the subscription for the clock topic
  void destroy_clock_sub()
  {
    std::lock_guard<std::mutex> guard(clock_sub_lock_);
    if (clock_executor_thread_.joinable()) {
      cancel_clock_executor_promise_.set_value();
      clock_executor_->cancel();
      clock_executor_thread_.join();
    }
    clock_subscription_.reset();
  }

  // An enum to hold the parameter state
  enum UseSimTimeParameterState { UNSET, SET_TRUE, SET_FALSE };
  UseSimTimeParameterState parameter_state_{UNSET};
};

TimeSource::TimeSource(agnocast::Node * node, const rclcpp::QoS & qos, bool use_clock_thread)
: TimeSource(qos, use_clock_thread)
{
  attachNode(node);
}

TimeSource::TimeSource(const rclcpp::QoS & qos, bool use_clock_thread)
: constructed_use_clock_thread_(use_clock_thread), constructed_qos_(qos)
{
  node_state_ = std::make_shared<NodeState>(qos, use_clock_thread);
}

void TimeSource::attachNode(agnocast::Node * node)
{
  attachNode(node->get_node_base_interface(), node->get_node_parameters_interface(), nullptr, node);
}

void TimeSource::attachNode(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_interface,
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr node_parameters_interface,
  rclcpp::node_interfaces::NodeClockInterface::SharedPtr node_clock_interface,
  agnocast::Node * node)
{
  node_state_->attachNode(
    std::move(node_base_interface), std::move(node_parameters_interface),
    std::move(node_clock_interface), node);
}

void TimeSource::detachNode()
{
  node_state_.reset();
  node_state_ = std::make_shared<NodeState>(constructed_qos_, constructed_use_clock_thread_);
}

void TimeSource::attachClock(std::shared_ptr<rclcpp::Clock> clock)
{
  node_state_->attachClock(std::move(clock));
}

void TimeSource::detachClock(std::shared_ptr<rclcpp::Clock> clock)
{
  node_state_->detachClock(std::move(clock));
}

bool TimeSource::get_use_clock_thread()
{
  return node_state_->get_use_clock_thread();
}

void TimeSource::set_use_clock_thread(bool use_clock_thread)
{
  node_state_->set_use_clock_thread(use_clock_thread);
}

bool TimeSource::clock_thread_is_joinable()
{
  return node_state_->clock_thread_is_joinable();
}

TimeSource::~TimeSource()
{
}

}  // namespace agnocast

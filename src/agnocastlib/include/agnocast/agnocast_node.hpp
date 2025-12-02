#pragma once

#include "agnocast/agnocast_context.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/node_options.hpp"
#include "rclcpp/rclcpp.hpp"

#include <map>
#include <memory>
#include <string>
#include <vector>

// New node interfaces (now inherit from rclcpp interfaces)
#include "agnocast/node_interfaces/node_base.hpp"
#include "agnocast/node_interfaces/node_parameters.hpp"
#include "agnocast/node_interfaces/node_topics.hpp"

namespace agnocast
{

// Parameter type constants (from rcl_interfaces/msg/ParameterType)
// Corresponds to ParameterType constants in ROS 2
// See: rcl_interfaces/msg/ParameterType.msg
constexpr uint8_t PARAMETER_NOT_SET = 0;
constexpr uint8_t PARAMETER_BOOL = 1;
constexpr uint8_t PARAMETER_INTEGER = 2;
constexpr uint8_t PARAMETER_DOUBLE = 3;
constexpr uint8_t PARAMETER_STRING = 4;
// Note: Array types (5-8) are not supported in agnocast

/**
 * @brief Simplified parameter descriptor (subset of rcl_interfaces::msg::ParameterDescriptor).
 */
struct ParameterDescriptor
{
  std::string description;
  bool read_only = false;
};

/**
 * @brief Internal struct for holding parameter information.
 */
struct ParameterInfo
{
  rclcpp::ParameterValue value;
  ParameterDescriptor descriptor;
};

class Node
{
public:
  using SharedPtr = std::shared_ptr<Node>;
  using ParameterValue = rclcpp::ParameterValue;

  explicit Node(
    const std::string & node_name, const rclcpp::NodeOptions & options = rclcpp::NodeOptions());

  explicit Node(
    const std::string & node_name, const std::string & namespace_,
    const rclcpp::NodeOptions & options = rclcpp::NodeOptions());

  std::string get_name() const { return node_base_->get_name(); }
  rclcpp::Logger get_logger() const { return logger_; }
  std::string get_namespace() const { return node_base_->get_namespace(); }
  std::string get_fully_qualified_name() const { return node_base_->get_fully_qualified_name(); }

  rclcpp::CallbackGroup::SharedPtr get_default_callback_group()
  {
    return node_base_->get_default_callback_group();
  }

  rclcpp::CallbackGroup::SharedPtr create_callback_group(
    rclcpp::CallbackGroupType group_type, bool automatically_add_to_executor_with_node = true)
  {
    return node_base_->create_callback_group(group_type, automatically_add_to_executor_with_node);
  }

  bool callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & group)
  {
    return node_base_->callback_group_in_node(group);
  }

  std::string resolve_topic_name(const std::string & input_topic_name) const
  {
    return node_topics_->resolve_topic_name(input_topic_name);
  }

  const ParameterValue & declare_parameter(
    const std::string & name, const ParameterValue & default_value,
    const ParameterDescriptor & descriptor = ParameterDescriptor{}, bool ignore_override = false);

  bool has_parameter(const std::string & name) const
  {
    return node_parameters_->has_parameter(name);
  }

  std::vector<uint8_t> get_parameter_types(const std::vector<std::string> & names) const
  {
    return node_parameters_->get_parameter_types(names);
  }

  bool get_parameter(const std::string & name, bool & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_BOOL) {
      return false;
    }
    value = param.as_bool();
    return true;
  }

  bool get_parameter(const std::string & name, int64_t & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_INTEGER) {
      return false;
    }
    value = param.as_int();
    return true;
  }

  bool get_parameter(const std::string & name, double & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_DOUBLE) {
      return false;
    }
    value = param.as_double();
    return true;
  }

  bool get_parameter(const std::string & name, std::string & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_STRING) {
      return false;
    }
    value = param.as_string();
    return true;
  }

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr get_node_base_interface()
  {
    return node_base_;
  }

  rclcpp::node_interfaces::NodeTopicsInterface::SharedPtr get_node_topics_interface()
  {
    return node_topics_;
  }

  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr get_node_parameters_interface()
  {
    return node_parameters_;
  }

  template <typename MessageT, typename Func>
  typename Subscription<MessageT>::SharedPtr create_subscription(
    const std::string & topic_name, size_t queue_size, Func && callback,
    SubscriptionOptions options);

private:
  void initialize_node(
    const std::string & node_name, const std::string & ns,
    rclcpp::Context::SharedPtr context = nullptr);

  rclcpp::Logger logger_{rclcpp::get_logger("agnocast_node")};
  node_interfaces::NodeBase::SharedPtr node_base_;
  node_interfaces::NodeTopics::SharedPtr node_topics_;
  node_interfaces::NodeParameters::SharedPtr node_parameters_;
};

}  // namespace agnocast

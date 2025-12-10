#pragma once

#include "agnocast/agnocast_context.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "agnocast/node_interfaces/node_base.hpp"
#include "agnocast/node_interfaces/node_parameters.hpp"
#include "agnocast/node_interfaces/node_topics.hpp"
#include "rcl_interfaces/msg/parameter_descriptor.hpp"
#include "rclcpp/node_options.hpp"
#include "rclcpp/rclcpp.hpp"

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace agnocast
{

// Use rcl_interfaces::msg::ParameterDescriptor directly for rclcpp API compatibility
using ParameterDescriptor = rcl_interfaces::msg::ParameterDescriptor;

/**
 * @brief Internal struct for holding parameter information.
 * Same structure as rclcpp::node_interfaces::ParameterInfo.
 */
struct ParameterInfo
{
  rclcpp::ParameterValue value;
  rcl_interfaces::msg::ParameterDescriptor descriptor;
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

  bool callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & callback_group)
  {
    return node_base_->callback_group_in_node(callback_group);
  }

  std::string resolve_topic_name(const std::string & input_topic_name) const
  {
    return node_topics_->resolve_topic_name(input_topic_name);
  }

  // ===== Parameter Declaration =====

  /// Declare and initialize a parameter, return the effective value.
  const ParameterValue & declare_parameter(
    const std::string & name, const ParameterValue & default_value,
    const ParameterDescriptor & descriptor = ParameterDescriptor{}, bool ignore_override = false);

  /// Declare and initialize a parameter with a type (templated version).
  template <typename ParameterT>
  ParameterT declare_parameter(
    const std::string & name, const ParameterT & default_value,
    const ParameterDescriptor & descriptor = ParameterDescriptor{}, bool ignore_override = false)
  {
    return this
      ->declare_parameter(name, rclcpp::ParameterValue(default_value), descriptor, ignore_override)
      .get<ParameterT>();
  }

  /// Undeclare a previously declared parameter.
  void undeclare_parameter(const std::string & name)
  {
    node_parameters_->undeclare_parameter(name);
  }

  /// Return true if a given parameter is declared.
  bool has_parameter(const std::string & name) const
  {
    return node_parameters_->has_parameter(name);
  }

  // ===== Parameter Setting =====

  /// Set a single parameter.
  rcl_interfaces::msg::SetParametersResult set_parameter(const rclcpp::Parameter & parameter)
  {
    auto results = node_parameters_->set_parameters({parameter});
    return results.front();
  }

  /// Set one or more parameters, one at a time.
  std::vector<rcl_interfaces::msg::SetParametersResult> set_parameters(
    const std::vector<rclcpp::Parameter> & parameters)
  {
    return node_parameters_->set_parameters(parameters);
  }

  /// Set one or more parameters, all at once.
  rcl_interfaces::msg::SetParametersResult set_parameters_atomically(
    const std::vector<rclcpp::Parameter> & parameters)
  {
    return node_parameters_->set_parameters_atomically(parameters);
  }

  // ===== Parameter Getting =====

  /// Return the parameter by the given name.
  rclcpp::Parameter get_parameter(const std::string & name) const
  {
    return node_parameters_->get_parameter(name);
  }

  /// Get the value of a parameter by the given name, and return true if it was set.
  bool get_parameter(const std::string & name, rclcpp::Parameter & parameter) const
  {
    return node_parameters_->get_parameter(name, parameter);
  }

  /// Get the value of a parameter by the given name (templated version).
  template <typename ParameterT>
  bool get_parameter(const std::string & name, ParameterT & parameter) const
  {
    rclcpp::Parameter param;
    bool result = node_parameters_->get_parameter(name, param);
    if (result) {
      parameter = param.get_value<ParameterT>();
    }
    return result;
  }

  /// Get the parameter value, or the "alternative_value" if not set.
  template <typename ParameterT>
  bool get_parameter_or(
    const std::string & name, ParameterT & parameter, const ParameterT & alternative_value) const
  {
    bool got_parameter = get_parameter(name, parameter);
    if (!got_parameter) {
      parameter = alternative_value;
    }
    return got_parameter;
  }

  /// Return the parameter value, or the "alternative_value" if not set.
  template <typename ParameterT>
  ParameterT get_parameter_or(const std::string & name, const ParameterT & alternative_value) const
  {
    ParameterT parameter;
    get_parameter_or(name, parameter, alternative_value);
    return parameter;
  }

  /// Return the parameters by the given parameter names.
  std::vector<rclcpp::Parameter> get_parameters(const std::vector<std::string> & names) const
  {
    return node_parameters_->get_parameters(names);
  }

  // ===== Parameter Description =====

  /// Return the parameter descriptor for the given parameter name.
  rcl_interfaces::msg::ParameterDescriptor describe_parameter(const std::string & name) const
  {
    auto descriptors = node_parameters_->describe_parameters({name});
    if (descriptors.front().type == rcl_interfaces::msg::ParameterType::PARAMETER_NOT_SET) {
      throw std::runtime_error("Parameter not declared: " + name);
    }
    return descriptors.front();
  }

  /// Return a vector of parameter descriptors, one for each of the given names.
  std::vector<rcl_interfaces::msg::ParameterDescriptor> describe_parameters(
    const std::vector<std::string> & names) const
  {
    return node_parameters_->describe_parameters(names);
  }

  /// Return a vector of parameter types, one for each of the given names.
  std::vector<uint8_t> get_parameter_types(const std::vector<std::string> & names) const
  {
    return node_parameters_->get_parameter_types(names);
  }

  /// Return a list of parameters with any of the given prefixes, up to the given depth.
  rcl_interfaces::msg::ListParametersResult list_parameters(
    const std::vector<std::string> & prefixes, uint64_t depth) const
  {
    return node_parameters_->list_parameters(prefixes, depth);
  }

  // Non-const to align with rclcpp::Node API
  // cppcheck-suppress functionConst
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
  typename agnocast::Subscription<MessageT>::SharedPtr create_subscription(
    const std::string & topic_name, size_t queue_size, Func && callback,
    agnocast::SubscriptionOptions options)
  {
    return std::make_shared<Subscription<MessageT>>(
      this, topic_name, rclcpp::QoS(rclcpp::KeepLast(queue_size)), std::forward<Func>(callback),
      options);
  }

  template <typename MessageT>
  typename agnocast::Publisher<MessageT>::SharedPtr create_publisher(
    const std::string & topic_name, size_t queue_size)
  {
    return std::make_shared<Publisher<MessageT>>(
      this, topic_name, rclcpp::QoS(rclcpp::KeepLast(queue_size)));
  }

private:
  void initialize_node(
    const std::string & node_name, const std::string & ns, const rclcpp::NodeOptions & options);

  void apply_remap_rules_from_arguments(const std::vector<std::string> & arguments);

  rclcpp::Logger logger_{rclcpp::get_logger("agnocast_node")};
  node_interfaces::NodeBase::SharedPtr node_base_;
  node_interfaces::NodeTopics::SharedPtr node_topics_;
  node_interfaces::NodeParameters::SharedPtr node_parameters_;
};

}  // namespace agnocast

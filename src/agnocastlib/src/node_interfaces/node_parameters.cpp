#include "agnocast/node_interfaces/node_parameters.hpp"

namespace agnocast::node_interfaces
{

NodeParameters::NodeParameters(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base)
: node_base_(node_base)
{
  // TODO
}

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, const rclcpp::ParameterValue & default_value,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  // TODO
}

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, rclcpp::ParameterType type,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  // TODO
}

void NodeParameters::undeclare_parameter(const std::string & name)
{
  // TODO
}

bool NodeParameters::has_parameter(const std::string & name) const
{
  // TODO
}

std::vector<rcl_interfaces::msg::SetParametersResult> NodeParameters::set_parameters(
  const std::vector<rclcpp::Parameter> & parameters)
{
  // TODO
}

rcl_interfaces::msg::SetParametersResult NodeParameters::set_parameters_atomically(
  const std::vector<rclcpp::Parameter> & parameters)
{
  // TODO
}

std::vector<rclcpp::Parameter> NodeParameters::get_parameters(
  const std::vector<std::string> & names) const
{
  // TODO
}

rclcpp::Parameter NodeParameters::get_parameter(const std::string & name) const
{
  // TODO
}

bool NodeParameters::get_parameter(const std::string & name, rclcpp::Parameter & parameter) const
{
  // TODO
}

bool NodeParameters::get_parameters_by_prefix(
  const std::string & prefix, std::map<std::string, rclcpp::Parameter> & parameters) const
{
  // TODO
}

std::vector<rcl_interfaces::msg::ParameterDescriptor> NodeParameters::describe_parameters(
  const std::vector<std::string> & names) const
{
  // TODO
}

std::vector<uint8_t> NodeParameters::get_parameter_types(
  const std::vector<std::string> & names) const
{
  // TODO
}

rcl_interfaces::msg::ListParametersResult NodeParameters::list_parameters(
  const std::vector<std::string> & prefixes, uint64_t depth) const
{
  // TODO
}

rclcpp::node_interfaces::OnSetParametersCallbackHandle::SharedPtr
NodeParameters::add_on_set_parameters_callback(OnParametersSetCallbackType callback)
{
  // TODO
}

void NodeParameters::remove_on_set_parameters_callback(
  const rclcpp::node_interfaces::OnSetParametersCallbackHandle * const handler)
{
  // TODO
}

const std::map<std::string, rclcpp::ParameterValue> & NodeParameters::get_parameter_overrides()
  const
{
  // TODO
}

void NodeParameters::add_parameter_override(const std::string & name, const ParameterValue & value)
{
  // TODO
}

}  // namespace agnocast::node_interfaces

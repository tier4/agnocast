#include "agnocast/node_interfaces/node_parameters.hpp"

#include "agnocast/agnocast_context.hpp"

namespace agnocast::node_interfaces
{

// TODO(Koichi98): In rclcpp, parameters are also loaded from NodeOptions::arguments()
// (e.g. --params-file). This is not yet implemented in agnocast.
std::map<std::string, rclcpp::ParameterValue> resolve_parameter_overrides(
  const std::string & node_fqn, const std::vector<rclcpp::Parameter> & parameter_overrides)
{
  std::map<std::string, rclcpp::ParameterValue> result;

  {
    std::lock_guard<std::mutex> lock(agnocast::g_context_mtx);
    if (agnocast::g_context.is_initialized()) {
      auto node_params = agnocast::g_context.get_param_overrides(node_fqn);
      for (const auto & [name, value] : node_params) {
        result[name] = value;
      }
    }
  }

  for (const auto & param : parameter_overrides) {
    result[param.get_name()] = param.get_parameter_value();
  }

  return result;
}

NodeParameters::NodeParameters(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base,
  const std::vector<rclcpp::Parameter> & parameter_overrides)
: node_base_(node_base)
{
  parameter_overrides_ =
    resolve_parameter_overrides(node_base->get_fully_qualified_name(), parameter_overrides);
}

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, const rclcpp::ParameterValue & default_value,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  // TODO(Koichi98)
  (void)name;
  (void)default_value;
  (void)parameter_descriptor;
  (void)ignore_override;
  throw std::runtime_error("NodeParameters::declare_parameter is not yet implemented in agnocast");
}

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, rclcpp::ParameterType type,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  // TODO(Koichi98)
  (void)name;
  (void)type;
  (void)parameter_descriptor;
  (void)ignore_override;
  throw std::runtime_error("NodeParameters::declare_parameter is not yet implemented in agnocast");
}

void NodeParameters::undeclare_parameter(const std::string & name)
{
  // TODO(Koichi98)
  (void)name;
  throw std::runtime_error(
    "NodeParameters::undeclare_parameter is not yet implemented in agnocast");
}

bool NodeParameters::has_parameter(const std::string & name) const
{
  // TODO(Koichi98)
  (void)name;
  throw std::runtime_error("NodeParameters::has_parameter is not yet implemented in agnocast");
}

std::vector<rcl_interfaces::msg::SetParametersResult> NodeParameters::set_parameters(
  const std::vector<rclcpp::Parameter> & parameters)
{
  // TODO(Koichi98)
  (void)parameters;
  throw std::runtime_error("NodeParameters::set_parameters is not yet implemented in agnocast");
}

rcl_interfaces::msg::SetParametersResult NodeParameters::set_parameters_atomically(
  const std::vector<rclcpp::Parameter> & parameters)
{
  // TODO(Koichi98)
  (void)parameters;
  throw std::runtime_error(
    "NodeParameters::set_parameters_atomically is not yet implemented in agnocast");
}

std::vector<rclcpp::Parameter> NodeParameters::get_parameters(
  const std::vector<std::string> & names) const
{
  // TODO(Koichi98)
  (void)names;
  throw std::runtime_error("NodeParameters::get_parameters is not yet implemented in agnocast");
}

rclcpp::Parameter NodeParameters::get_parameter(const std::string & name) const
{
  // TODO(Koichi98)
  (void)name;
  throw std::runtime_error("NodeParameters::get_parameter is not yet implemented in agnocast");
}

bool NodeParameters::get_parameter(const std::string & name, rclcpp::Parameter & parameter) const
{
  // TODO(Koichi98)
  (void)name;
  (void)parameter;
  throw std::runtime_error("NodeParameters::get_parameter is not yet implemented in agnocast");
}

bool NodeParameters::get_parameters_by_prefix(
  const std::string & prefix, std::map<std::string, rclcpp::Parameter> & parameters) const
{
  // TODO(Koichi98)
  (void)prefix;
  (void)parameters;
  throw std::runtime_error(
    "NodeParameters::get_parameters_by_prefix is not yet implemented in agnocast");
}

std::vector<rcl_interfaces::msg::ParameterDescriptor> NodeParameters::describe_parameters(
  const std::vector<std::string> & names) const
{
  // TODO(Koichi98)
  (void)names;
  throw std::runtime_error(
    "NodeParameters::describe_parameters is not yet implemented in agnocast");
}

std::vector<uint8_t> NodeParameters::get_parameter_types(
  const std::vector<std::string> & names) const
{
  // TODO(Koichi98)
  (void)names;
  throw std::runtime_error(
    "NodeParameters::get_parameter_types is not yet implemented in agnocast");
}

rcl_interfaces::msg::ListParametersResult NodeParameters::list_parameters(
  const std::vector<std::string> & prefixes, uint64_t depth) const
{
  // TODO(Koichi98)
  (void)prefixes;
  (void)depth;
  throw std::runtime_error("NodeParameters::list_parameters is not yet implemented in agnocast");
}

rclcpp::node_interfaces::OnSetParametersCallbackHandle::SharedPtr
NodeParameters::add_on_set_parameters_callback(OnParametersSetCallbackType callback)
{
  // TODO(Koichi98)
  (void)callback;
  throw std::runtime_error(
    "NodeParameters::add_on_set_parameters_callback is not yet implemented in agnocast");
}

void NodeParameters::remove_on_set_parameters_callback(
  const rclcpp::node_interfaces::OnSetParametersCallbackHandle * const handler)
{
  // TODO(Koichi98)
  (void)handler;
  throw std::runtime_error(
    "NodeParameters::remove_on_set_parameters_callback is not yet implemented in agnocast");
}

const std::map<std::string, rclcpp::ParameterValue> & NodeParameters::get_parameter_overrides()
  const
{
  return parameter_overrides_;
}

}  // namespace agnocast::node_interfaces

#include "agnocast/node_interfaces/node_parameters.hpp"

#include "agnocast/agnocast_node.hpp"  // For ParameterDescriptor and ParameterInfo definitions

#include <yaml.h>

#include <cstdio>
#include <stdexcept>

namespace agnocast
{
namespace node_interfaces
{

// Parameter type constants (matching rcl_interfaces/msg/ParameterType)
constexpr uint8_t PARAMETER_NOT_SET = 0;
constexpr uint8_t PARAMETER_BOOL = 1;
constexpr uint8_t PARAMETER_INTEGER = 2;
constexpr uint8_t PARAMETER_DOUBLE = 3;
constexpr uint8_t PARAMETER_STRING = 4;

NodeParameters::NodeParameters(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base)
: node_base_(node_base)
{
}

// ===== rclcpp interface methods =====

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, const rclcpp::ParameterValue & default_value,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  // Convert to internal format and declare
  ParameterValue internal_value = convert_from_rclcpp_value(default_value);
  declare_parameter_simple(
    name, internal_value, parameter_descriptor.description, parameter_descriptor.read_only,
    ignore_override);

  // Get the actual value (may be overridden)
  auto it = parameters_.find(name);
  if (it != parameters_.end()) {
    last_declared_value_ = convert_to_rclcpp_value(it->second.value);
  } else {
    last_declared_value_ = default_value;
  }
  return last_declared_value_;
}

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, rclcpp::ParameterType type,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  (void)parameter_descriptor;
  (void)ignore_override;

  // Create a default value based on type
  rclcpp::ParameterValue default_value;
  switch (type) {
    case rclcpp::ParameterType::PARAMETER_BOOL:
      default_value = rclcpp::ParameterValue(false);
      break;
    case rclcpp::ParameterType::PARAMETER_INTEGER:
      default_value = rclcpp::ParameterValue(static_cast<int64_t>(0));
      break;
    case rclcpp::ParameterType::PARAMETER_DOUBLE:
      default_value = rclcpp::ParameterValue(0.0);
      break;
    case rclcpp::ParameterType::PARAMETER_STRING:
      default_value = rclcpp::ParameterValue(std::string(""));
      break;
    default:
      throw std::runtime_error("Unsupported parameter type in agnocast");
  }

  return declare_parameter(name, default_value, parameter_descriptor, ignore_override);
}

void NodeParameters::undeclare_parameter(const std::string & name)
{
  auto it = parameters_.find(name);
  if (it != parameters_.end()) {
    if (it->second.descriptor.read_only) {
      throw std::runtime_error("Cannot undeclare read-only parameter: " + name);
    }
    parameters_.erase(it);
  }
}

bool NodeParameters::has_parameter(const std::string & name) const
{
  return parameters_.find(name) != parameters_.end();
}

std::vector<rcl_interfaces::msg::SetParametersResult> NodeParameters::set_parameters(
  const std::vector<rclcpp::Parameter> & parameters)
{
  std::vector<rcl_interfaces::msg::SetParametersResult> results;
  for (const auto & param : parameters) {
    rcl_interfaces::msg::SetParametersResult result;
    auto it = parameters_.find(param.get_name());
    if (it != parameters_.end() && it->second.descriptor.read_only) {
      result.successful = false;
      result.reason = "Parameter is read-only";
    } else {
      ParameterValue value = convert_from_rclcpp_value(param.get_parameter_value());
      if (it != parameters_.end()) {
        it->second.value = value;
      } else {
        parameters_[param.get_name()] = ParameterInfo{value, {}};
      }
      result.successful = true;
    }
    results.push_back(result);
  }
  return results;
}

rcl_interfaces::msg::SetParametersResult NodeParameters::set_parameters_atomically(
  const std::vector<rclcpp::Parameter> & parameters)
{
  rcl_interfaces::msg::SetParametersResult result;

  // Check all parameters first
  for (const auto & param : parameters) {
    auto it = parameters_.find(param.get_name());
    if (it != parameters_.end() && it->second.descriptor.read_only) {
      result.successful = false;
      result.reason = "Parameter " + param.get_name() + " is read-only";
      return result;
    }
  }

  // Set all parameters
  for (const auto & param : parameters) {
    ParameterValue value = convert_from_rclcpp_value(param.get_parameter_value());
    auto it = parameters_.find(param.get_name());
    if (it != parameters_.end()) {
      it->second.value = value;
    } else {
      parameters_[param.get_name()] = ParameterInfo{value, {}};
    }
  }

  result.successful = true;
  return result;
}

std::vector<rclcpp::Parameter> NodeParameters::get_parameters(
  const std::vector<std::string> & names) const
{
  std::vector<rclcpp::Parameter> result;
  for (const auto & name : names) {
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      result.push_back(rclcpp::Parameter(name, convert_to_rclcpp_value(it->second.value)));
    }
  }
  return result;
}

rclcpp::Parameter NodeParameters::get_parameter(const std::string & name) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    throw std::runtime_error("Parameter not found: " + name);
  }
  return rclcpp::Parameter(name, convert_to_rclcpp_value(it->second.value));
}

bool NodeParameters::get_parameter(const std::string & name, rclcpp::Parameter & parameter) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }
  parameter = rclcpp::Parameter(name, convert_to_rclcpp_value(it->second.value));
  return true;
}

bool NodeParameters::get_parameters_by_prefix(
  const std::string & prefix, std::map<std::string, rclcpp::Parameter> & parameters) const
{
  bool found = false;
  for (const auto & [name, info] : parameters_) {
    if (name.rfind(prefix, 0) == 0) {
      // Remove prefix and separator
      std::string suffix = name.substr(prefix.length());
      if (!suffix.empty() && suffix[0] == '.') {
        suffix = suffix.substr(1);
      }
      parameters[suffix] = rclcpp::Parameter(name, convert_to_rclcpp_value(info.value));
      found = true;
    }
  }
  return found;
}

std::vector<rcl_interfaces::msg::ParameterDescriptor> NodeParameters::describe_parameters(
  const std::vector<std::string> & names) const
{
  std::vector<rcl_interfaces::msg::ParameterDescriptor> result;
  for (const auto & name : names) {
    rcl_interfaces::msg::ParameterDescriptor desc;
    desc.name = name;
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      desc.description = it->second.descriptor.description;
      desc.read_only = it->second.descriptor.read_only;
      // Determine type
      if (std::holds_alternative<bool>(it->second.value)) {
        desc.type = PARAMETER_BOOL;
      } else if (std::holds_alternative<int64_t>(it->second.value)) {
        desc.type = PARAMETER_INTEGER;
      } else if (std::holds_alternative<double>(it->second.value)) {
        desc.type = PARAMETER_DOUBLE;
      } else if (std::holds_alternative<std::string>(it->second.value)) {
        desc.type = PARAMETER_STRING;
      }
    }
    result.push_back(desc);
  }
  return result;
}

std::vector<uint8_t> NodeParameters::get_parameter_types(
  const std::vector<std::string> & names) const
{
  std::vector<uint8_t> types;
  types.reserve(names.size());

  for (const auto & name : names) {
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      const auto & value = it->second.value;
      if (std::holds_alternative<bool>(value)) {
        types.push_back(PARAMETER_BOOL);
      } else if (std::holds_alternative<int64_t>(value)) {
        types.push_back(PARAMETER_INTEGER);
      } else if (std::holds_alternative<double>(value)) {
        types.push_back(PARAMETER_DOUBLE);
      } else if (std::holds_alternative<std::string>(value)) {
        types.push_back(PARAMETER_STRING);
      } else {
        types.push_back(PARAMETER_NOT_SET);
      }
    } else {
      types.push_back(PARAMETER_NOT_SET);
    }
  }

  return types;
}

rcl_interfaces::msg::ListParametersResult NodeParameters::list_parameters(
  const std::vector<std::string> & prefixes, uint64_t depth) const
{
  (void)depth;
  rcl_interfaces::msg::ListParametersResult result;

  for (const auto & [name, info] : parameters_) {
    (void)info;
    if (prefixes.empty()) {
      result.names.push_back(name);
    } else {
      for (const auto & prefix : prefixes) {
        if (name.rfind(prefix, 0) == 0) {
          result.names.push_back(name);
          break;
        }
      }
    }
  }

  return result;
}

rclcpp::node_interfaces::OnSetParametersCallbackHandle::SharedPtr
NodeParameters::add_on_set_parameters_callback(OnParametersSetCallbackType callback)
{
  (void)callback;
  throw std::runtime_error(
    "NodeParameters::add_on_set_parameters_callback is not yet supported in agnocast");
}

void NodeParameters::remove_on_set_parameters_callback(
  const rclcpp::node_interfaces::OnSetParametersCallbackHandle * const handler)
{
  (void)handler;
  throw std::runtime_error(
    "NodeParameters::remove_on_set_parameters_callback is not yet supported in agnocast");
}

const std::map<std::string, rclcpp::ParameterValue> & NodeParameters::get_parameter_overrides()
  const
{
  return parameter_overrides_rclcpp_;
}

// ===== Agnocast-specific methods =====

void NodeParameters::declare_parameter_simple(
  const std::string & name, const ParameterValue & default_value, const std::string & description,
  bool read_only, bool ignore_override)
{
  // Check if parameter already exists
  if (parameters_.find(name) != parameters_.end()) {
    return;
  }

  ParameterInfo param_info;
  param_info.descriptor.description = description;
  param_info.descriptor.read_only = read_only;

  // Check for command-line override
  if (
    !ignore_override &&
    parameter_overrides_internal_.find(name) != parameter_overrides_internal_.end()) {
    param_info.value = parameter_overrides_internal_[name];
  } else {
    param_info.value = default_value;
  }

  parameters_[name] = param_info;
}

bool NodeParameters::get_parameter(const std::string & name, bool & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<bool>(&it->second.value)) {
    value = *v;
    return true;
  }
  return false;
}

bool NodeParameters::get_parameter(const std::string & name, int64_t & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<int64_t>(&it->second.value)) {
    value = *v;
    return true;
  }
  return false;
}

bool NodeParameters::get_parameter(const std::string & name, double & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<double>(&it->second.value)) {
    value = *v;
    return true;
  }
  return false;
}

bool NodeParameters::get_parameter(const std::string & name, std::string & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<std::string>(&it->second.value)) {
    value = *v;
    return true;
  }
  return false;
}

void NodeParameters::add_parameter_override(const std::string & name, const ParameterValue & value)
{
  parameter_overrides_internal_[name] = value;
  parameter_overrides_rclcpp_[name] = convert_to_rclcpp_value(value);
}

bool NodeParameters::load_parameters_from_yaml_file(const std::string & file_path)
{
  (void)file_path;
  return false;  // Not implemented
}

// ===== Private methods =====

NodeParameters::ParameterValue NodeParameters::parse_parameter_value(
  const std::string & value_str) const
{
  // Try to parse as bool
  if (value_str == "true" || value_str == "True" || value_str == "TRUE") {
    return true;
  }
  if (value_str == "false" || value_str == "False" || value_str == "FALSE") {
    return false;
  }

  // Try to parse as integer
  try {
    size_t pos = 0;
    int64_t int_value = std::stoll(value_str, &pos);
    if (pos == value_str.length()) {
      return int_value;
    }
  } catch (...) {
  }

  // Try to parse as double
  try {
    size_t pos = 0;
    double double_value = std::stod(value_str, &pos);
    if (pos == value_str.length()) {
      return double_value;
    }
  } catch (...) {
  }

  // Default to string
  return value_str;
}

rclcpp::ParameterValue NodeParameters::convert_to_rclcpp_value(const ParameterValue & value) const
{
  if (auto * v = std::get_if<bool>(&value)) {
    return rclcpp::ParameterValue(*v);
  } else if (auto * v = std::get_if<int64_t>(&value)) {
    return rclcpp::ParameterValue(*v);
  } else if (auto * v = std::get_if<double>(&value)) {
    return rclcpp::ParameterValue(*v);
  } else if (auto * v = std::get_if<std::string>(&value)) {
    return rclcpp::ParameterValue(*v);
  }
  return rclcpp::ParameterValue();
}

NodeParameters::ParameterValue NodeParameters::convert_from_rclcpp_value(
  const rclcpp::ParameterValue & value) const
{
  switch (value.get_type()) {
    case rclcpp::ParameterType::PARAMETER_BOOL:
      return value.get<bool>();
    case rclcpp::ParameterType::PARAMETER_INTEGER:
      return value.get<int64_t>();
    case rclcpp::ParameterType::PARAMETER_DOUBLE:
      return value.get<double>();
    case rclcpp::ParameterType::PARAMETER_STRING:
      return value.get<std::string>();
    default:
      return std::string("");
  }
}

}  // namespace node_interfaces
}  // namespace agnocast

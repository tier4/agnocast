#include "agnocast/node_interfaces/node_parameters.hpp"

#include "agnocast/agnocast_context.hpp"
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

namespace
{

/// Validate a parameter value against its descriptor's range constraints.
/// Returns empty string if valid, or error message if invalid.
std::string validate_parameter_range(
  const rclcpp::ParameterValue & value, const rcl_interfaces::msg::ParameterDescriptor & descriptor)
{
  // Check floating point range
  if (!descriptor.floating_point_range.empty()) {
    const auto & range = descriptor.floating_point_range[0];
    double val = 0.0;

    if (value.get_type() == rclcpp::ParameterType::PARAMETER_DOUBLE) {
      val = value.get<double>();
    } else if (value.get_type() == rclcpp::ParameterType::PARAMETER_INTEGER) {
      val = static_cast<double>(value.get<int64_t>());
    } else {
      return "";  // Range check only applies to numeric types
    }

    if (val < range.from_value || val > range.to_value) {
      return "Parameter value " + std::to_string(val) + " is out of range [" +
             std::to_string(range.from_value) + ", " + std::to_string(range.to_value) + "]";
    }

    // Check step constraint if specified (step > 0)
    if (range.step > 0.0) {
      double offset = val - range.from_value;
      double remainder = std::fmod(offset, range.step);
      // Allow small floating point tolerance
      if (remainder > 1e-9 && (range.step - remainder) > 1e-9) {
        return "Parameter value " + std::to_string(val) +
               " does not match step constraint (step=" + std::to_string(range.step) + ")";
      }
    }
  }

  // Check integer range
  if (!descriptor.integer_range.empty()) {
    const auto & range = descriptor.integer_range[0];

    if (value.get_type() != rclcpp::ParameterType::PARAMETER_INTEGER) {
      return "";  // Integer range check only applies to integer type
    }

    int64_t val = value.get<int64_t>();

    if (val < range.from_value || val > range.to_value) {
      return "Parameter value " + std::to_string(val) + " is out of range [" +
             std::to_string(range.from_value) + ", " + std::to_string(range.to_value) + "]";
    }

    // Check step constraint if specified (step > 0)
    if (range.step > 0) {
      int64_t offset = val - range.from_value;
      if (offset % static_cast<int64_t>(range.step) != 0) {
        return "Parameter value " + std::to_string(val) +
               " does not match step constraint (step=" + std::to_string(range.step) + ")";
      }
    }
  }

  return "";  // Valid
}

}  // namespace

NodeParameters::NodeParameters(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base)
: node_base_(node_base)
{
}

// ===== rclcpp interface methods =====

const rclcpp::ParameterValue & NodeParameters::declare_parameter(
  const std::string & name, const rclcpp::ParameterValue & default_value,
  const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor, bool ignore_override)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);

  // Declare the parameter using internal method (without lock since we already hold it)
  // Inline the logic from declare_parameter_simple to avoid double locking
  if (parameters_.find(name) == parameters_.end()) {
    ParameterInfo param_info;
    param_info.descriptor = parameter_descriptor;

    // Check for command-line override
    if (!ignore_override && parameter_overrides_.find(name) != parameter_overrides_.end()) {
      param_info.value = parameter_overrides_[name];
    } else {
      param_info.value = default_value;
    }

    parameters_[name] = param_info;
  }

  // Return reference to value in the map (stable as long as entry exists)
  return parameters_[name].value;
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
  std::lock_guard<std::mutex> lock(g_context_mtx);
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
  std::lock_guard<std::mutex> lock(g_context_mtx);
  return parameters_.find(name) != parameters_.end();
}

std::vector<rcl_interfaces::msg::SetParametersResult> NodeParameters::set_parameters(
  const std::vector<rclcpp::Parameter> & parameters)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  std::vector<rcl_interfaces::msg::SetParametersResult> results;
  for (const auto & param : parameters) {
    rcl_interfaces::msg::SetParametersResult result;
    auto it = parameters_.find(param.get_name());

    // Check read-only
    if (it != parameters_.end() && it->second.descriptor.read_only) {
      result.successful = false;
      result.reason = "Parameter is read-only";
      results.push_back(result);
      continue;
    }

    // Check range constraints (only for existing parameters with descriptors)
    if (it != parameters_.end()) {
      std::string validation_error =
        validate_parameter_range(param.get_parameter_value(), it->second.descriptor);
      if (!validation_error.empty()) {
        result.successful = false;
        result.reason = validation_error;
        results.push_back(result);
        continue;
      }
      it->second.value = param.get_parameter_value();
    } else {
      parameters_[param.get_name()] =
        ParameterInfo{param.get_parameter_value(), rcl_interfaces::msg::ParameterDescriptor()};
    }
    result.successful = true;
    results.push_back(result);
  }
  return results;
}

rcl_interfaces::msg::SetParametersResult NodeParameters::set_parameters_atomically(
  const std::vector<rclcpp::Parameter> & parameters)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  rcl_interfaces::msg::SetParametersResult result;

  // Check all parameters first (read-only and range constraints)
  for (const auto & param : parameters) {
    auto it = parameters_.find(param.get_name());
    if (it != parameters_.end()) {
      // Check read-only
      if (it->second.descriptor.read_only) {
        result.successful = false;
        result.reason = "Parameter " + param.get_name() + " is read-only";
        return result;
      }
      // Check range constraints
      std::string validation_error =
        validate_parameter_range(param.get_parameter_value(), it->second.descriptor);
      if (!validation_error.empty()) {
        result.successful = false;
        result.reason = "Parameter " + param.get_name() + ": " + validation_error;
        return result;
      }
    }
  }

  // Set all parameters (validation passed)
  for (const auto & param : parameters) {
    auto it = parameters_.find(param.get_name());
    if (it != parameters_.end()) {
      it->second.value = param.get_parameter_value();
    } else {
      parameters_[param.get_name()] =
        ParameterInfo{param.get_parameter_value(), rcl_interfaces::msg::ParameterDescriptor()};
    }
  }

  result.successful = true;
  return result;
}

std::vector<rclcpp::Parameter> NodeParameters::get_parameters(
  const std::vector<std::string> & names) const
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  std::vector<rclcpp::Parameter> result;
  for (const auto & name : names) {
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      result.push_back(rclcpp::Parameter(name, it->second.value));
    }
  }
  return result;
}

rclcpp::Parameter NodeParameters::get_parameter(const std::string & name) const
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    throw std::runtime_error("Parameter not found: " + name);
  }
  return rclcpp::Parameter(name, it->second.value);
}

bool NodeParameters::get_parameter(const std::string & name, rclcpp::Parameter & parameter) const
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }
  parameter = rclcpp::Parameter(name, it->second.value);
  return true;
}

bool NodeParameters::get_parameters_by_prefix(
  const std::string & prefix, std::map<std::string, rclcpp::Parameter> & parameters) const
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  bool found = false;
  for (const auto & [name, info] : parameters_) {
    if (name.rfind(prefix, 0) == 0) {
      // Remove prefix and separator
      std::string suffix = name.substr(prefix.length());
      if (!suffix.empty() && suffix[0] == '.') {
        suffix = suffix.substr(1);
      }
      parameters[suffix] = rclcpp::Parameter(name, info.value);
      found = true;
    }
  }
  return found;
}

std::vector<rcl_interfaces::msg::ParameterDescriptor> NodeParameters::describe_parameters(
  const std::vector<std::string> & names) const
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  std::vector<rcl_interfaces::msg::ParameterDescriptor> result;
  for (const auto & name : names) {
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      // Copy the stored descriptor (includes all fields)
      rcl_interfaces::msg::ParameterDescriptor desc = it->second.descriptor;
      desc.name = name;
      // Set type from actual value
      switch (it->second.value.get_type()) {
        case rclcpp::ParameterType::PARAMETER_BOOL:
          desc.type = PARAMETER_BOOL;
          break;
        case rclcpp::ParameterType::PARAMETER_INTEGER:
          desc.type = PARAMETER_INTEGER;
          break;
        case rclcpp::ParameterType::PARAMETER_DOUBLE:
          desc.type = PARAMETER_DOUBLE;
          break;
        case rclcpp::ParameterType::PARAMETER_STRING:
          desc.type = PARAMETER_STRING;
          break;
        default:
          desc.type = PARAMETER_NOT_SET;
          break;
      }
      result.push_back(desc);
    } else {
      // Parameter not found - return empty descriptor with just the name
      rcl_interfaces::msg::ParameterDescriptor desc;
      desc.name = name;
      desc.type = PARAMETER_NOT_SET;
      result.push_back(desc);
    }
  }
  return result;
}

std::vector<uint8_t> NodeParameters::get_parameter_types(
  const std::vector<std::string> & names) const
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  std::vector<uint8_t> types;
  types.reserve(names.size());

  for (const auto & name : names) {
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      switch (it->second.value.get_type()) {
        case rclcpp::ParameterType::PARAMETER_BOOL:
          types.push_back(PARAMETER_BOOL);
          break;
        case rclcpp::ParameterType::PARAMETER_INTEGER:
          types.push_back(PARAMETER_INTEGER);
          break;
        case rclcpp::ParameterType::PARAMETER_DOUBLE:
          types.push_back(PARAMETER_DOUBLE);
          break;
        case rclcpp::ParameterType::PARAMETER_STRING:
          types.push_back(PARAMETER_STRING);
          break;
        default:
          types.push_back(PARAMETER_NOT_SET);
          break;
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
  std::lock_guard<std::mutex> lock(g_context_mtx);
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
  std::lock_guard<std::mutex> lock(g_context_mtx);
  return parameter_overrides_;
}

// ===== Agnocast-specific methods =====

void NodeParameters::declare_parameter_simple(
  const std::string & name, const ParameterValue & default_value, const std::string & description,
  bool read_only, bool ignore_override)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  // Check if parameter already exists
  if (parameters_.find(name) != parameters_.end()) {
    return;
  }

  ParameterInfo param_info;
  param_info.descriptor.description = description;
  param_info.descriptor.read_only = read_only;

  // Check for command-line override
  if (!ignore_override && parameter_overrides_.find(name) != parameter_overrides_.end()) {
    param_info.value = parameter_overrides_[name];
  } else {
    param_info.value = default_value;
  }

  parameters_[name] = param_info;
}

void NodeParameters::add_parameter_override(const std::string & name, const ParameterValue & value)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  parameter_overrides_[name] = value;
}

}  // namespace node_interfaces
}  // namespace agnocast

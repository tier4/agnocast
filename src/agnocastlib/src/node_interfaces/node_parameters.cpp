// Copyright 2025 Agnocast Contributors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "agnocast/node_interfaces/node_parameters.hpp"

#include "agnocast/agnocast_node.hpp"  // For ParameterDescriptor and ParameterInfo definitions

#include <yaml.h>

#include <cstdio>

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

void NodeParameters::declare_parameter(
  const std::string & name, const ParameterValue & default_value, const std::string & description,
  bool read_only, bool ignore_override)
{
  // Corresponds to NodeParameters::declare_parameter in
  // rclcpp/src/rclcpp/node_interfaces/node_parameters.cpp

  // Check if parameter already exists
  if (parameters_.find(name) != parameters_.end()) {
    // Parameter already declared, do nothing
    return;
  }

  ParameterInfo param_info;
  param_info.descriptor.description = description;
  param_info.descriptor.read_only = read_only;

  // Check for command-line override (unless ignore_override is true)
  if (!ignore_override && parameter_overrides_.find(name) != parameter_overrides_.end()) {
    param_info.value = parameter_overrides_[name];
  } else {
    param_info.value = default_value;
  }

  parameters_[name] = param_info;
}

bool NodeParameters::has_parameter(const std::string & name) const
{
  // Corresponds to NodeParameters::has_parameter in
  // rclcpp/include/rclcpp/node_interfaces/node_parameters.hpp:130
  return parameters_.find(name) != parameters_.end();
}

std::vector<uint8_t> NodeParameters::get_parameter_types(
  const std::vector<std::string> & names) const
{
  // Corresponds to NodeParameters::get_parameter_types in
  // rclcpp/src/rclcpp/node_interfaces/node_parameters.cpp:896-919

  std::vector<uint8_t> types;
  types.reserve(names.size());

  for (const auto & name : names) {
    auto it = parameters_.find(name);
    if (it != parameters_.end()) {
      // Determine type from variant index
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

bool NodeParameters::get_parameter(const std::string & name, bool & value) const
{
  // Corresponds to NodeParameters::get_parameter in
  // rclcpp/src/rclcpp/node_interfaces/node_parameters.cpp:829-845

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
  parameter_overrides_[name] = value;
}

NodeParameters::ParameterValue NodeParameters::parse_parameter_value(
  const std::string & value_str) const
{
  // Corresponds to rcl_parse_yaml_value in rcl_yaml_param_parser/src/parser.c
  // Performs type inference in this order:
  // 1. Boolean: "true", "True", "TRUE", "false", "False", "FALSE"
  // 2. Integer: valid int64_t (e.g., "42", "-10")
  // 3. Double: valid double (e.g., "3.14", "1.0")
  // 4. String: anything else (e.g., "hello")

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

bool NodeParameters::load_parameters_from_yaml_file(const std::string & file_path)
{
  // Corresponds to rcl_parse_yaml_file in rcl_yaml_param_parser/src/parser.c
  // This is a simplified implementation - copy the full implementation from agnocast_node.cpp
  // For now, return false (not implemented)
  (void)file_path;
  return false;
}

}  // namespace node_interfaces
}  // namespace agnocast

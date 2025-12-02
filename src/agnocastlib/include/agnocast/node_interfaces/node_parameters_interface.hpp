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

#ifndef AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_INTERFACE_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_INTERFACE_HPP_

#include <memory>
#include <string>
#include <variant>
#include <vector>

namespace agnocast
{
namespace node_interfaces
{

/// Pure virtual interface class for the NodeParameters part of the Node API.
class NodeParametersInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeParametersInterface>;
  using WeakPtr = std::weak_ptr<NodeParametersInterface>;
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  virtual ~NodeParametersInterface() = default;

  /// Declare a parameter with a default value.
  /**
   * Corresponds to rclcpp::Node::declare_parameter.
   *
   * \param name Parameter name
   * \param default_value Default value
   * \param description Optional parameter description
   * \param read_only Whether the parameter is read-only
   * \param ignore_override When true, ignore command-line/YAML overrides and use default_value
   */
  virtual void declare_parameter(
    const std::string & name, const ParameterValue & default_value,
    const std::string & description = "", bool read_only = false, bool ignore_override = false) = 0;

  /// Check if a parameter has been declared.
  /**
   * \param name Parameter name
   * \return true if parameter exists, false otherwise
   */
  virtual bool has_parameter(const std::string & name) const = 0;

  /// Get parameter types for a list of parameter names.
  /**
   * Corresponds to rclcpp::Node::get_parameter_types.
   *
   * \param names Vector of parameter names
   * \return Vector of parameter type IDs
   */
  virtual std::vector<uint8_t> get_parameter_types(
    const std::vector<std::string> & names) const = 0;

  /// Get a parameter value by name.
  /**
   * \param name Parameter name
   * \param value Output parameter value
   * \return true if parameter exists, false otherwise
   */
  virtual bool get_parameter(const std::string & name, bool & value) const = 0;

  virtual bool get_parameter(const std::string & name, int64_t & value) const = 0;

  virtual bool get_parameter(const std::string & name, double & value) const = 0;

  virtual bool get_parameter(const std::string & name, std::string & value) const = 0;
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_INTERFACE_HPP_

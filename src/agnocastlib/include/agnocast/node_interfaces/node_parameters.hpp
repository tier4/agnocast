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

#ifndef AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_HPP_

#include "rclcpp/node_interfaces/node_base_interface.hpp"
#include "rclcpp/node_interfaces/node_parameters_interface.hpp"

#include <map>
#include <memory>
#include <string>
#include <variant>
#include <vector>

namespace agnocast
{

// Forward declarations (actual definitions in agnocast_node.hpp)
struct ParameterDescriptor;
struct ParameterInfo;

namespace node_interfaces
{

/// Implementation of the NodeParameters part of the Node API.
/// Inherits from rclcpp::node_interfaces::NodeParametersInterface for compatibility.
class NodeParameters : public rclcpp::node_interfaces::NodeParametersInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeParameters>;
  using WeakPtr = std::weak_ptr<NodeParameters>;
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  /**
   * @brief Construct a NodeParameters.
   *
   * @param node_base Pointer to the node base interface
   */
  explicit NodeParameters(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base);

  virtual ~NodeParameters() = default;

  // ===== Implemented methods =====

  const rclcpp::ParameterValue & declare_parameter(
    const std::string & name, const rclcpp::ParameterValue & default_value,
    const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor =
      rcl_interfaces::msg::ParameterDescriptor(),
    bool ignore_override = false) override;

  const rclcpp::ParameterValue & declare_parameter(
    const std::string & name, rclcpp::ParameterType type,
    const rcl_interfaces::msg::ParameterDescriptor & parameter_descriptor =
      rcl_interfaces::msg::ParameterDescriptor(),
    bool ignore_override = false) override;

  void undeclare_parameter(const std::string & name) override;

  bool has_parameter(const std::string & name) const override;

  std::vector<rcl_interfaces::msg::SetParametersResult> set_parameters(
    const std::vector<rclcpp::Parameter> & parameters) override;

  rcl_interfaces::msg::SetParametersResult set_parameters_atomically(
    const std::vector<rclcpp::Parameter> & parameters) override;

  std::vector<rclcpp::Parameter> get_parameters(
    const std::vector<std::string> & names) const override;

  rclcpp::Parameter get_parameter(const std::string & name) const override;

  bool get_parameter(const std::string & name, rclcpp::Parameter & parameter) const override;

  bool get_parameters_by_prefix(
    const std::string & prefix,
    std::map<std::string, rclcpp::Parameter> & parameters) const override;

  std::vector<rcl_interfaces::msg::ParameterDescriptor> describe_parameters(
    const std::vector<std::string> & names) const override;

  std::vector<uint8_t> get_parameter_types(const std::vector<std::string> & names) const override;

  rcl_interfaces::msg::ListParametersResult list_parameters(
    const std::vector<std::string> & prefixes, uint64_t depth) const override;

  rclcpp::node_interfaces::OnSetParametersCallbackHandle::SharedPtr add_on_set_parameters_callback(
    OnParametersSetCallbackType callback) override;

  void remove_on_set_parameters_callback(
    const rclcpp::node_interfaces::OnSetParametersCallbackHandle * const handler) override;

  const std::map<std::string, rclcpp::ParameterValue> & get_parameter_overrides() const override;

  // ===== Agnocast-specific methods =====

  /**
   * @brief Declare a parameter with agnocast's simple ParameterValue type.
   */
  void declare_parameter_simple(
    const std::string & name, const ParameterValue & default_value,
    const std::string & description = "", bool read_only = false, bool ignore_override = false);

  /**
   * @brief Get a parameter value by name (type-specific overloads).
   */
  bool get_parameter(const std::string & name, bool & value) const;
  bool get_parameter(const std::string & name, int64_t & value) const;
  bool get_parameter(const std::string & name, double & value) const;
  bool get_parameter(const std::string & name, std::string & value) const;

  /**
   * @brief Add a parameter override.
   *
   * @param name Parameter name
   * @param value Parameter value
   */
  void add_parameter_override(const std::string & name, const ParameterValue & value);

  /**
   * @brief Load parameters from a YAML file.
   *
   * @param file_path Path to the YAML parameter file
   * @return true if file was loaded successfully, false otherwise
   */
  bool load_parameters_from_yaml_file(const std::string & file_path);

private:
  ParameterValue parse_parameter_value(const std::string & value_str) const;
  rclcpp::ParameterValue convert_to_rclcpp_value(const ParameterValue & value) const;
  ParameterValue convert_from_rclcpp_value(const rclcpp::ParameterValue & value) const;

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  std::map<std::string, ParameterInfo> parameters_;
  std::map<std::string, ParameterValue> parameter_overrides_internal_;
  std::map<std::string, rclcpp::ParameterValue> parameter_overrides_rclcpp_;
  rclcpp::ParameterValue last_declared_value_;  // For return reference
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_HPP_

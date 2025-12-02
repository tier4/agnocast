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

#include "agnocast/node_interfaces/node_parameters_interface.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"

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
class NodeParameters : public NodeParametersInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeParameters>;
  using WeakPtr = std::weak_ptr<NodeParameters>;

  /**
   * @brief Construct a NodeParameters.
   *
   * @param node_base Pointer to the node base interface
   */
  explicit NodeParameters(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base);

  virtual ~NodeParameters() = default;

  void declare_parameter(
    const std::string & name, const ParameterValue & default_value,
    const std::string & description = "", bool read_only = false,
    bool ignore_override = false) override;

  bool has_parameter(const std::string & name) const override;

  std::vector<uint8_t> get_parameter_types(const std::vector<std::string> & names) const override;

  bool get_parameter(const std::string & name, bool & value) const override;

  bool get_parameter(const std::string & name, int64_t & value) const override;

  bool get_parameter(const std::string & name, double & value) const override;

  bool get_parameter(const std::string & name, std::string & value) const override;

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
  /**
   * @brief Parse a parameter value string to appropriate type.
   *
   * @param value_str String representation of the value
   * @return Parsed parameter value
   */
  ParameterValue parse_parameter_value(const std::string & value_str) const;

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  std::map<std::string, ParameterInfo> parameters_;
  std::map<std::string, ParameterValue> parameter_overrides_;
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_PARAMETERS_HPP_

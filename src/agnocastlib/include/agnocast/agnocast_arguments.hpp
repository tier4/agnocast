#pragma once

#include <rclcpp/parameter.hpp>
#include <rclcpp/parameter_value.hpp>

#include <rcl/arguments.h>
#include <rcl_yaml_param_parser/parser.h>
#include <rcl_yaml_param_parser/types.h>

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace agnocast
{

enum class RemapType { NODE_NAME, NAMESPACE, TOPIC_OR_SERVICE };

struct RemapRule
{
  RemapType type;
  std::string node_name;  // Node name prefix (empty means global rule)
  std::string match;
  std::string replacement;
};

using ParameterValue = rclcpp::ParameterValue;

/// RAII wrapper for rcl_params_t.
/// Corresponds to rcl_params_t usage in rclcpp/rcl.
class ParameterOverrides
{
public:
  ParameterOverrides();
  ~ParameterOverrides();

  // Copy semantics (using rcl_yaml_node_struct_copy)
  ParameterOverrides(const ParameterOverrides & other);
  ParameterOverrides & operator=(const ParameterOverrides & other);

  // Move semantics
  ParameterOverrides(ParameterOverrides && other) noexcept;
  ParameterOverrides & operator=(ParameterOverrides && other) noexcept;

  /// Get the underlying rcl_params_t pointer.
  rcl_params_t * get() const { return params_; }

  /// Parse a YAML parameter file and add parameters to the structure.
  /// Corresponds to rcl_parse_yaml_file.
  /// @param yaml_file Path to the YAML file
  /// @return true if successful, false otherwise
  bool parse_yaml_file(const std::string & yaml_file);

  /// Parse a parameter rule (e.g., "param_name:=value" or "node_name:param_name:=value").
  /// Corresponds to rcl_parse_yaml_value with node name prefix support.
  /// @param arg The argument string to parse
  /// @return true if successful, false otherwise
  bool parse_param_rule(const std::string & arg);

private:
  rcl_params_t * params_;
};

struct ParsedArguments
{
  std::vector<RemapRule> remap_rules;
  ParameterOverrides parameter_overrides;

  // Default constructor
  ParsedArguments() = default;

  // Copy and move semantics (ParameterOverrides supports both)
  ParsedArguments(const ParsedArguments &) = default;
  ParsedArguments & operator=(const ParsedArguments &) = default;
  ParsedArguments(ParsedArguments &&) = default;
  ParsedArguments & operator=(ParsedArguments &&) = default;
};

bool parse_remap_rule(const std::string & arg, RemapRule & output_rule);

ParsedArguments parse_arguments(const std::vector<std::string> & arguments);

/// Resolve parameter overrides from multiple sources.
/// Corresponds to rclcpp::detail::resolve_parameter_overrides.
/// Priority (later overwrites earlier): global_args < local_args < parameter_overrides
/// @param node_fqn Fully qualified name of the node (used for node-specific filtering)
/// @param parameter_overrides Parameters from NodeOptions::parameter_overrides()
/// @param local_args Parsed arguments from NodeOptions::arguments()
/// @param global_args Parsed arguments from command line (via agnocast::init)
std::map<std::string, ParameterValue> resolve_parameter_overrides(
  const std::string & node_fqn, const std::vector<rclcpp::Parameter> & parameter_overrides,
  const ParsedArguments & local_args, const ParsedArguments & global_args);

}  // namespace agnocast

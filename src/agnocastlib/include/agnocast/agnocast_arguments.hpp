#pragma once

#include <rclcpp/parameter.hpp>
#include <rclcpp/parameter_value.hpp>

#include <rcl/arguments.h>

#include <map>
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

struct ParsedArguments
{
  std::vector<RemapRule> remap_rules;
  std::map<std::string, ParameterValue> parameter_overrides;
};

ParameterValue parse_parameter_value(const std::string & value_str);
bool parse_remap_rule(const std::string & arg, RemapRule & output_rule);
bool parse_param_rule(
  const std::string & arg, std::string & param_name, ParameterValue & param_value);

ParsedArguments parse_arguments(const std::vector<std::string> & arguments);

/// Resolve parameter overrides from multiple sources.
/// Corresponds to rclcpp::detail::resolve_parameter_overrides.
/// Priority (later overwrites earlier): global_args < local_args < parameter_overrides
/// @param node_fqn Fully qualified name of the node (for future node-specific filtering:
/// TODO(Koichi98))
/// @param parameter_overrides Parameters from NodeOptions::parameter_overrides()
/// @param local_args Parsed arguments from NodeOptions::arguments()
/// @param global_args Parsed arguments from command line (via agnocast::init)
std::map<std::string, ParameterValue> resolve_parameter_overrides(
  const std::string & node_fqn, const std::vector<rclcpp::Parameter> & parameter_overrides,
  const ParsedArguments & local_args, const ParsedArguments & global_args);

}  // namespace agnocast

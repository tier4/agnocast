#pragma once

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

ParsedArguments parse_arguments(const std::vector<std::string> & arguments);

ParameterValue parse_parameter_value(const std::string & value_str);
bool parse_remap_rule(const std::string & arg, RemapRule & output_rule);
bool parse_param_rule(
  const std::string & arg, std::string & param_name, ParameterValue & param_value);

}  // namespace agnocast

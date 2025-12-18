#include "agnocast/agnocast_arguments.hpp"

#include <rcl_yaml_param_parser/parser.h>
#include <rcl_yaml_param_parser/types.h>
#include <rcutils/allocator.h>

#include <algorithm>
#include <array>
#include <functional>

namespace agnocast
{

namespace
{

// RCL argument flags (corresponds to rcl/arguments.h)
constexpr const char * RCL_ROS_ARGS_FLAG = "--ros-args";
constexpr const char * RCL_ROS_ARGS_EXPLICIT_END_TOKEN = "--";
constexpr const char * RCL_PARAM_FLAG = "--param";
constexpr const char * RCL_SHORT_PARAM_FLAG = "-p";
constexpr const char * RCL_REMAP_FLAG = "--remap";
constexpr const char * RCL_SHORT_REMAP_FLAG = "-r";
constexpr const char * RCL_PARAM_FILE_FLAG = "--params-file";

/// Parse node name prefix from parameter rule.
/// Returns the node name and advances pos past the colon.
/// If no prefix found, returns "/**" (match all nodes).
std::string parse_node_name_prefix(const std::string & arg, size_t & pos)
{
  // Look for pattern: token ':' (not ':=')
  size_t colon_pos = arg.find(':', pos);
  size_t separator_pos = arg.find(":=", pos);

  // If ':' exists and is before ':=', it's a node name prefix
  if (colon_pos != std::string::npos && colon_pos < separator_pos) {
    std::string node_name = arg.substr(pos, colon_pos - pos);
    pos = colon_pos + 1;
    return node_name;
  }

  // No node name prefix, match all nodes
  return "/**";
}

/// RAII wrapper for rcl_params_t.
/// Used internally by parse_arguments.
class ParameterOverrides
{
public:
  ParameterOverrides()
  {
    rcutils_allocator_t allocator = rcutils_get_default_allocator();
    params_ = rcl_yaml_node_struct_init(allocator);
    if (nullptr == params_) {
      throw std::runtime_error("Failed to initialize rcl_params_t");
    }
  }

  ~ParameterOverrides()
  {
    if (params_) {
      rcl_yaml_node_struct_fini(params_);
      params_ = nullptr;
    }
  }

  // Non-copyable, non-movable (only used locally)
  ParameterOverrides(const ParameterOverrides &) = delete;
  ParameterOverrides & operator=(const ParameterOverrides &) = delete;
  ParameterOverrides(ParameterOverrides &&) = delete;
  ParameterOverrides & operator=(ParameterOverrides &&) = delete;

  bool parse_yaml_file(const std::string & yaml_file)
  {
    return rcl_parse_yaml_file(yaml_file.c_str(), params_);
  }

  bool parse_param_rule(const std::string & arg)
  {
    // Format: [node_name:]param_name:=yaml_value
    size_t pos = 0;
    std::string node_name = parse_node_name_prefix(arg, pos);

    size_t separator_pos = arg.find(":=", pos);
    if (separator_pos == std::string::npos) {
      return false;
    }

    std::string param_name = arg.substr(pos, separator_pos - pos);
    std::string yaml_value = arg.substr(separator_pos + 2);

    if (param_name.empty()) {
      return false;
    }

    return rcl_parse_yaml_value(node_name.c_str(), param_name.c_str(), yaml_value.c_str(), params_);
  }

private:
  rcl_params_t * params_;
};

}  // namespace

bool parse_remap_rule(const std::string & arg, RemapRule & output_rule)
{
  // Corresponds to _rcl_parse_remap_rule in rcl/src/rcl/arguments.c.
  size_t separator = arg.find(":=");
  if (separator == std::string::npos) {
    return false;
  }

  std::string from = arg.substr(0, separator);
  std::string to = arg.substr(separator + 2);

  RemapRule rule;
  rule.replacement = to;

  size_t colon_pos = from.find(':');
  if (colon_pos != std::string::npos && colon_pos < separator) {
    if (!from.empty() && from[0] != '/') {
      rule.node_name = from.substr(0, colon_pos);
      rule.match = from.substr(colon_pos + 1);
    } else {
      rule.match = from;
    }
  } else {
    rule.match = from;
  }

  if (rule.match == "__node" || rule.match == "__name") {
    rule.type = RemapType::NODE_NAME;
    rule.node_name.clear();  // __node/__name rules are always global
  } else if (rule.match == "__ns") {
    rule.type = RemapType::NAMESPACE;
    rule.node_name.clear();  // __ns rules are always global
  } else {
    rule.type = RemapType::TOPIC_OR_SERVICE;
  }

  output_rule = rule;
  return true;
}

ParsedArguments parse_arguments(const std::vector<std::string> & arguments)
{
  // Corresponds to rcl_parse_arguments in rcl/src/rcl/arguments.c
  ParsedArguments result;
  ParameterOverrides param_overrides;

  bool parsing_ros_args = false;
  for (size_t i = 0; i < arguments.size(); ++i) {
    const std::string & arg = arguments[i];

    if (parsing_ros_args) {
      // Ignore ROS specific arguments flag
      if (arg == RCL_ROS_ARGS_FLAG) {
        continue;
      }

      // Check for ROS specific arguments explicit end token
      if (arg == RCL_ROS_ARGS_EXPLICIT_END_TOKEN) {
        parsing_ros_args = false;
        continue;
      }

      // Attempt to parse argument as parameter file flag
      if (arg == RCL_PARAM_FILE_FLAG && i + 1 < arguments.size()) {
        ++i;
        param_overrides.parse_yaml_file(arguments[i]);
        continue;
      }

      // Attempt to parse argument as parameter override flag
      if ((arg == RCL_PARAM_FLAG || arg == RCL_SHORT_PARAM_FLAG) && i + 1 < arguments.size()) {
        ++i;
        param_overrides.parse_param_rule(arguments[i]);
        continue;
      }

      // Attempt to parse argument as remap rule flag
      if ((arg == RCL_REMAP_FLAG || arg == RCL_SHORT_REMAP_FLAG) && i + 1 < arguments.size()) {
        ++i;
        RemapRule rule;
        if (parse_remap_rule(arguments[i], rule)) {
          result.remap_rules.push_back(rule);
        }
        continue;
      }

      // TODO(Koichi98): Parse other ROS specific arguments.

    } else {
      // Check for ROS specific arguments flag
      if (arg == RCL_ROS_ARGS_FLAG) {
        parsing_ros_args = true;
        continue;
      }

      // Argument is not a ROS specific argument
      // In RCL this would be stored in unparsed_args
    }
  }

  return result;
}

std::map<std::string, ParameterValue> resolve_parameter_overrides(
  const std::string & node_fqn, const std::vector<rclcpp::Parameter> & parameter_overrides,
  const ParsedArguments & local_args, const ParsedArguments & global_args)
{
  // Corresponds to rclcpp/src/rclcpp/detail/resolve_parameter_overrides.cpp
  //
  // TODO(Koichi98): node_fqn is currently unused. In rclcpp, node_fqn is used to filter
  // parameters by node name. This requires:
  // - YAML parser support (--params-file)
  // - Node name prefix support ("node_name:param_name:=value" format)
  // Currently, all parameters are applied globally to all nodes.
  (void)node_fqn;

  std::map<std::string, ParameterValue> result;

  // global before local so that local overwrites global
  std::array<std::reference_wrapper<const ParsedArguments>, 2> argument_sources = {
    std::cref(global_args), std::cref(local_args)};

  for (const ParsedArguments & source : argument_sources) {
    for (const auto & [name, value] : source.parameter_overrides) {
      result[name] = value;
    }
  }

  // parameter overrides passed to constructor will overwrite overrides from yaml file sources
  for (const auto & param : parameter_overrides) {
    result[param.get_name()] = rclcpp::ParameterValue(param.get_value_message());
  }

  return result;
}

}  // namespace agnocast

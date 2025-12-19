#include "agnocast/agnocast_arguments.hpp"

#include <rcutils/allocator.h>
#include <rcutils/logging_macros.h>

#include <algorithm>
#include <array>
#include <functional>
#include <regex>
#include <sstream>

namespace agnocast
{

namespace
{

/// Convert rcl_variant_t to rclcpp::ParameterValue.
ParameterValue parameter_value_from(const rcl_variant_t * c_param_value)
{
  if (nullptr == c_param_value) {
    throw std::invalid_argument("Passed argument is NULL");
  }
  if (c_param_value->bool_value) {
    return ParameterValue(*(c_param_value->bool_value));
  } else if (c_param_value->integer_value) {
    return ParameterValue(*(c_param_value->integer_value));
  } else if (c_param_value->double_value) {
    return ParameterValue(*(c_param_value->double_value));
  } else if (c_param_value->string_value) {
    return ParameterValue(std::string(c_param_value->string_value));
  } else if (c_param_value->byte_array_value) {
    const rcl_byte_array_t * byte_array = c_param_value->byte_array_value;
    std::vector<uint8_t> bytes;
    bytes.reserve(byte_array->size);
    for (size_t v = 0; v < byte_array->size; ++v) {
      bytes.push_back(byte_array->values[v]);
    }
    return ParameterValue(bytes);
  } else if (c_param_value->bool_array_value) {
    const rcl_bool_array_t * bool_array = c_param_value->bool_array_value;
    std::vector<bool> bools;
    bools.reserve(bool_array->size);
    for (size_t v = 0; v < bool_array->size; ++v) {
      bools.push_back(bool_array->values[v]);
    }
    return ParameterValue(bools);
  } else if (c_param_value->integer_array_value) {
    const rcl_int64_array_t * int_array = c_param_value->integer_array_value;
    std::vector<int64_t> integers;
    integers.reserve(int_array->size);
    for (size_t v = 0; v < int_array->size; ++v) {
      integers.push_back(int_array->values[v]);
    }
    return ParameterValue(integers);
  } else if (c_param_value->double_array_value) {
    const rcl_double_array_t * double_array = c_param_value->double_array_value;
    std::vector<double> doubles;
    doubles.reserve(double_array->size);
    for (size_t v = 0; v < double_array->size; ++v) {
      doubles.push_back(double_array->values[v]);
    }
    return ParameterValue(doubles);
  } else if (c_param_value->string_array_value) {
    const rcutils_string_array_t * string_array = c_param_value->string_array_value;
    std::vector<std::string> strings;
    strings.reserve(string_array->size);
    for (size_t v = 0; v < string_array->size; ++v) {
      strings.emplace_back(string_array->data[v]);
    }
    return ParameterValue(strings);
  }

  throw std::runtime_error("No parameter value set");
}

/// Convert node name pattern to regex.
std::string node_pattern_to_regex(const std::string & node_name)
{
  std::string result;
  result.reserve(node_name.size() * 2);

  for (size_t i = 0; i < node_name.size(); ++i) {
    if (node_name[i] == '/' && i + 1 < node_name.size() && node_name[i + 1] == '*') {
      if (i + 2 < node_name.size() && node_name[i + 2] == '*') {
        // "/**" -> "(/\\w+)*"
        result += "(/\\w+)*";
        i += 2;
      } else {
        // "/*" -> "(/\\w+)"
        result += "(/\\w+)";
        i += 1;
      }
    } else if (node_name[i] == '.') {
      // Escape '.' for regex
      result += "\\.";
    } else {
      result += node_name[i];
    }
  }

  return result;
}

std::string parse_node_name_prefix(const std::string & arg, size_t & pos)
{
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

}  // namespace

ParameterOverrides::ParameterOverrides()
{
  rcutils_allocator_t allocator = rcutils_get_default_allocator();
  params_ = rcl_yaml_node_struct_init(allocator);
  if (nullptr == params_) {
    throw std::runtime_error("Failed to initialize rcl_params_t");
  }
}

ParameterOverrides::~ParameterOverrides()
{
  if (params_ != nullptr) {
    rcl_yaml_node_struct_fini(params_);
    params_ = nullptr;
  }
}

ParameterOverrides::ParameterOverrides(const ParameterOverrides & other) : params_(nullptr)
{
  if (other.params_ != nullptr) {
    params_ = rcl_yaml_node_struct_copy(other.params_);
    if (nullptr == params_) {
      throw std::runtime_error("Failed to copy rcl_params_t");
    }
  }
}

ParameterOverrides & ParameterOverrides::operator=(const ParameterOverrides & other)
{
  if (this != &other) {
    if (params_ != nullptr) {
      rcl_yaml_node_struct_fini(params_);
      params_ = nullptr;
    }
    if (other.params_ != nullptr) {
      params_ = rcl_yaml_node_struct_copy(other.params_);
      if (nullptr == params_) {
        throw std::runtime_error("Failed to copy rcl_params_t");
      }
    }
  }
  return *this;
}

ParameterOverrides::ParameterOverrides(ParameterOverrides && other) noexcept
: params_(other.params_)
{
  other.params_ = nullptr;
}

ParameterOverrides & ParameterOverrides::operator=(ParameterOverrides && other) noexcept
{
  if (this != &other) {
    if (params_ != nullptr) {
      rcl_yaml_node_struct_fini(params_);
    }
    params_ = other.params_;
    other.params_ = nullptr;
  }
  return *this;
}

bool ParameterOverrides::parse_yaml_file(const std::string & yaml_file)
{
  return rcl_parse_yaml_file(yaml_file.c_str(), params_);
}

bool ParameterOverrides::parse_param_rule(const std::string & arg)
{
  size_t pos = 0;
  std::string node_name = parse_node_name_prefix(arg, pos);

  // Find the separator ':='
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

// Free functions

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
        if (!result.parameter_overrides.parse_yaml_file(arguments[i])) {
          RCUTILS_LOG_WARN_NAMED(
            "agnocast", "Failed to parse params file: %s", arguments[i].c_str());
        }
        continue;
      }

      // Attempt to parse argument as parameter override flag
      if ((arg == RCL_PARAM_FLAG || arg == RCL_SHORT_PARAM_FLAG) && i + 1 < arguments.size()) {
        ++i;
        if (!result.parameter_overrides.parse_param_rule(arguments[i])) {
          RCUTILS_LOG_WARN_NAMED(
            "agnocast", "Failed to parse parameter rule: %s", arguments[i].c_str());
        }
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

std::map<std::string, ParameterValue> parameter_map_from(
  const rcl_params_t * params, const std::string & node_fqn)
{
  // Corresponds to rclcpp::parameter_map_from in rclcpp/parameter_map.cpp
  std::map<std::string, ParameterValue> result;

  if (nullptr == params || nullptr == params->node_names || nullptr == params->params) {
    return result;
  }

  for (size_t n = 0; n < params->num_nodes; ++n) {
    const char * c_node_name = params->node_names[n];
    if (nullptr == c_node_name) {
      continue;
    }

    // Make sure there is a leading slash on the node name
    std::string node_name("/");
    if ('/' != c_node_name[0]) {
      node_name += c_node_name;
    } else {
      node_name = c_node_name;
    }

    // Check if node name pattern matches the target node FQN
    // Convert pattern to regex: "/*" -> "(/\\w+)" and "/**" -> "(/\\w+)*"
    std::string regex_pattern = node_pattern_to_regex(node_name);
    if (!std::regex_match(node_fqn, std::regex(regex_pattern))) {
      continue;
    }

    const rcl_node_params_t * c_params_node = &(params->params[n]);

    for (size_t p = 0; p < c_params_node->num_params; ++p) {
      const char * c_param_name = c_params_node->parameter_names[p];
      if (nullptr == c_param_name) {
        continue;
      }

      const rcl_variant_t * c_param_value = &(c_params_node->parameter_values[p]);
      try {
        result[c_param_name] = parameter_value_from(c_param_value);
      } catch (const std::exception &) {
        // Skip parameters that can't be converted
        // TODO(Koichi98): Add proper logging
      }
    }
  }

  return result;
}

std::map<std::string, ParameterValue> resolve_parameter_overrides(
  const std::string & node_fqn, const std::vector<rclcpp::Parameter> & parameter_overrides,
  const ParsedArguments & local_args, const ParsedArguments & global_args)
{
  // Corresponds to rclcpp/src/rclcpp/detail/resolve_parameter_overrides.cpp
  // NOTE: node_fqn, local_args, and global_args are intentionally unused for now.
  // They will be consumed by parameter_map_from once it is implemented to resolve
  // parameter overrides from YAML/CLI sources scoped to the given node FQN.
  (void)node_fqn;
  (void)local_args;
  (void)global_args;

  std::map<std::string, ParameterValue> result;

  // TODO(Koichi98): Implement a helper equivalent to rclcpp::detail::parameter_map_from
  // (see rclcpp/src/rclcpp/detail/resolve_parameter_overrides.cpp in
  // https://github.com/ros2/rclcpp/blob/rolling/rclcpp/src/rclcpp/detail/resolve_parameter_overrides.cpp)
  // and use it here to filter parameters by node FQN from global_args and local_args.

  // Parameter overrides passed to constructor will overwrite overrides from yaml file sources
  for (const auto & param : parameter_overrides) {
    result[param.get_name()] = rclcpp::ParameterValue(param.get_value_message());
  }

  return result;
}

}  // namespace agnocast

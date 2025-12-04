#include "agnocast/agnocast_context.hpp"

#include <algorithm>
#include <cctype>
#include <sstream>

namespace agnocast
{

Context g_context;
std::mutex g_context_mtx;

void Context::init(int argc, char const * const * argv)
{
  // Corresponds to rcl_parse_arguments in rcl/src/rcl/arguments.c
  if (initialized_) {
    return;
  }

  // Copy argv into a safe container to avoid pointer arithmetic
  std::vector<std::string> args;
  args.reserve(static_cast<size_t>(argc));
  for (int i = 0; i < argc; ++i) {
    args.emplace_back(argv[i]);  // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
  }

  bool parsing_ros_args = false;
  for (int i = 0; i < argc; ++i) {
    const std::string & arg = args[static_cast<size_t>(i)];

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

      // Attempt to parse argument as parameter override flag
      if ((arg == RCL_PARAM_FLAG || arg == RCL_SHORT_PARAM_FLAG) && i + 1 < argc) {
        i++;
        std::string param_arg = args[static_cast<size_t>(i)];
        parse_param_rule(param_arg);
        continue;
      }

      // Attempt to parse argument as remap rule flag
      if ((arg == RCL_REMAP_FLAG || arg == RCL_SHORT_REMAP_FLAG) && i + 1 < argc) {
        i++;
        std::string remap_arg = args[static_cast<size_t>(i)];
        parse_remap_rule(remap_arg);
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

  initialized_ = true;
}

bool Context::parse_param_rule(const std::string & arg)
{
  // Corresponds to _rcl_parse_param_rule in rcl/src/rcl/arguments.c.
  //
  // Limitations compared to rcl:
  // - No yaml parser: arrays (e.g., [1,2,3]) are not supported, only scalar values.
  // - No node name prefix: "node_name:param_name:=value" format is not supported.

  size_t delim_pos = arg.find(":=");

  if (delim_pos == std::string::npos) {
    return false;
  }

  std::string param_name = arg.substr(0, delim_pos);
  std::string yaml_value = arg.substr(delim_pos + 2);

  global_parameter_overrides_[param_name] = parse_parameter_value(yaml_value);
  return true;
}

Context::ParameterValue Context::parse_parameter_value(const std::string & value_str)
{
  std::string lower_value = value_str;
  std::transform(lower_value.begin(), lower_value.end(), lower_value.begin(), [](unsigned char c) {
    return std::tolower(c);
  });

  if (lower_value == "true") {
    return rclcpp::ParameterValue(true);
  }
  if (lower_value == "false") {
    return rclcpp::ParameterValue(false);
  }

  {
    std::istringstream iss(value_str);
    int64_t int_value = 0;
    if (iss >> int_value && iss.eof()) {
      return rclcpp::ParameterValue(int_value);
    }
  }

  {
    std::istringstream iss(value_str);
    double double_value = 0.0;
    if (iss >> double_value && iss.eof()) {
      return rclcpp::ParameterValue(double_value);
    }
  }

  return rclcpp::ParameterValue(value_str);
}

bool Context::parse_remap_rule(const std::string & arg)
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
    // TODO(Koichi98): This is a temporary workaround to maintain compatibility with the existing
    // node name remapping logic. This will be removed once a more robust remap handling is
    // implemented.
    {
      std::lock_guard<std::mutex> lock(g_context_mtx);
      command_line_params.node_name = to;
    }
  } else if (rule.match == "__ns") {
    rule.type = RemapType::NAMESPACE;
    rule.node_name.clear();  // __ns rules are always global
  } else {
    rule.type = RemapType::TOPIC_OR_SERVICE;
  }

  remap_rules_.push_back(rule);

  return true;
}

void init(int argc, char const * const * argv)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  g_context.init(argc, argv);
}

}  // namespace agnocast

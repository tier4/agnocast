#include "agnocast/agnocast_context.hpp"

#include <algorithm>
#include <cctype>
#include <charconv>

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

  std::string node_name;
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
        ++i;  // Skip to argument value
        std::string remap_arg = args[static_cast<size_t>(i)];
        parse_remap_rule(remap_arg);
        continue;
      }

      // TODO(Koichi98): Will be replaced with a more robust remap parsing logic following rcl's
      // implementation.
      if (arg == "-r" && i + 1 < argc) {
        std::string remap{args[static_cast<size_t>(i) + 1]};
        const std::string prefix = "__node:=";

        if (remap.compare(0, prefix.size(), prefix) == 0) {
          node_name = remap.substr(prefix.size());

          {
            std::lock_guard<std::mutex> lock(g_context_mtx);
            g_context.command_line_params.node_name = node_name;
          }

          break;
        }
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

  int64_t int_value;
  auto int_result =
    std::from_chars(value_str.data(), value_str.data() + value_str.size(), int_value);
  if (int_result.ec == std::errc{} && int_result.ptr == value_str.data() + value_str.size()) {
    return rclcpp::ParameterValue(int_value);
  }

  double double_value;
  auto double_result =
    std::from_chars(value_str.data(), value_str.data() + value_str.size(), double_value);
  if (double_result.ec == std::errc{} && double_result.ptr == value_str.data() + value_str.size()) {
    return rclcpp::ParameterValue(double_value);
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
  rule.match = from;
  rule.replacement = to;

  if (from == "__node" || from == "__name") {
    rule.type = RemapType::NODENAME;
  } else if (from == "__ns") {
    rule.type = RemapType::NAMESPACE;
  } else {
    rule.type = RemapType::TOPIC;
  }

  remap_rules_.push_back(rule);
  return true;
}

void init(int argc, char const * const * argv)
{
  g_context.init(argc, argv);
}

}  // namespace agnocast

#include "agnocast/agnocast_context.hpp"

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
      if (arg == AGNOCAST_ROS_ARGS_FLAG) {
        continue;
      }

      // Check for ROS specific arguments explicit end token
      if (arg == AGNOCAST_ROS_ARGS_EXPLICIT_END_TOKEN) {
        parsing_ros_args = false;
        continue;
      }

      // Attempt to parse argument as parameter override flag
      if ((arg == AGNOCAST_PARAM_FLAG || arg == AGNOCAST_SHORT_PARAM_FLAG) && i + 1 < argc) {
        std::string param_arg = argv[++i];
        parse_param_rule(param_arg);  // Parse immediately
        continue;
      }

      // TODO: Will be replaced with a more robust remap parsing logic following rcl's
      // implementation.
      if (arg == "-r" && i + 1 < argc) {
        std::string remap{args[static_cast<size_t>(i + 1)]};
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

      // TODO: Parse other ROS specific arguments.

    } else {
      // Check for ROS specific arguments flag
      if (arg == AGNOCAST_ROS_ARGS_FLAG) {
        parsing_ros_args = true;
        continue;
      }

      // Argument is not a ROS specific argument
      // In RCL this would be stored in unparsed_args
    }
  }

  initialized_ = true;
}

bool GlobalContext::parse_param_rule(const std::string & arg)
{
  // Corresponds to _rcl_parse_param_rule in rcl/src/rcl/arguments.c.

  size_t delim_pos = arg.find(":=");

  if (delim_pos == std::string::npos) {
    return false;
  }

  std::string param_name = arg.substr(0, delim_pos);
  std::string yaml_value = arg.substr(delim_pos + 2);

  // Store in global_parameter_overrides_ (applied to all nodes)
  global_parameter_overrides_[param_name] = parse_parameter_value(yaml_value);
  return true;
}

GlobalContext::ParameterValue GlobalContext::parse_parameter_value(const std::string & value_str)
{
  if (value_str == "true" || value_str == "True" || value_str == "TRUE") {
    return true;
  }
  if (value_str == "false" || value_str == "False" || value_str == "FALSE") {
    return false;
  }

  try {
    size_t pos = 0;
    int64_t int_value = std::stoll(value_str, &pos);
    if (pos == value_str.length()) {
      return int_value;
    }
  } catch (...) {
  }

  try {
    size_t pos = 0;
    double double_value = std::stod(value_str, &pos);
    if (pos == value_str.length()) {
      return double_value;
    }
  } catch (...) {
  }

  return value_str;
}

void init(int argc, char const * const * argv)
{
  g_context.init(argc, argv);
}

}  // namespace agnocast

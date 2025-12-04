#include "agnocast/agnocast_context.hpp"

#include <rclcpp/logging.hpp>

#include <yaml.h>

#include <algorithm>
#include <cctype>
#include <charconv>

namespace agnocast
{
Context g_context;
std::mutex g_context_mtx;

Context & Context::instance()
{
  return g_context;
}

void Context::init(int argc, char const * const * argv)
{
  // Corresponds to rcl_parse_arguments in rcl/src/rcl/arguments.c
  if (initialized_.load(std::memory_order_acquire)) {
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
        ++i;  // Skip to argument value
        std::string param_arg = args[static_cast<size_t>(i)];
        if (!parse_param_rule(param_arg)) {
          RCLCPP_WARN(
            rclcpp::get_logger("agnocast"), "Failed to parse parameter rule: '%s'",
            param_arg.c_str());
        }
        continue;
      }

      // Attempt to parse argument as remap rule flag
      if ((arg == RCL_REMAP_FLAG || arg == RCL_SHORT_REMAP_FLAG) && i + 1 < argc) {
        ++i;  // Skip to argument value
        std::string remap_arg = args[static_cast<size_t>(i)];
        if (!parse_remap_rule(remap_arg)) {
          RCLCPP_WARN(
            rclcpp::get_logger("agnocast"), "Failed to parse remap rule: '%s'", remap_arg.c_str());
        }
        continue;
      }

      // Attempt to parse argument as parameter file rule
      if (arg == RCL_PARAM_FILE_FLAG && i + 1 < argc) {
        ++i;  // Skip to argument value
        std::string file_path = args[static_cast<size_t>(i)];
        if (!parse_yaml_file(file_path)) {
          RCLCPP_WARN(
            rclcpp::get_logger("agnocast"), "Failed to parse YAML parameter file: '%s'",
            file_path.c_str());
        }
        continue;
      }

      // Unknown ROS specific argument - skip it
      // In RCL this would be stored in unparsed_ros_args

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

  initialized_.store(true, std::memory_order_release);
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

  // Check for node name prefix (format: "node_name:/topic:=/new_topic")
  // ROS2 remap format: [node_name:]match:=replacement
  size_t colon_pos = from.find(':');
  if (colon_pos != std::string::npos && colon_pos < separator) {
    // There's a colon in the match part - check if it's a node prefix
    // Node prefix format: "node_name:/topic" or "node_name:topic"
    // Not a node prefix if it starts with "/" (absolute topic with colon in name)
    if (from[0] != '/') {
      rule.node_name = from.substr(0, colon_pos);
      rule.match = from.substr(colon_pos + 1);
    } else {
      rule.match = from;
    }
  } else {
    rule.match = from;
  }

  if (rule.match == "__node" || rule.match == "__name") {
    rule.type = RemapType::NODENAME;
    rule.node_name.clear();  // __node/__name rules are always global
  } else if (rule.match == "__ns") {
    rule.type = RemapType::NAMESPACE;
    rule.node_name.clear();  // __ns rules are always global
  } else {
    rule.type = RemapType::TOPIC_OR_SERVICE;
  }

  remap_rules_.push_back(rule);
  return true;
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

  // Store in global_parameter_overrides_ (applied to all nodes)
  global_parameter_overrides_[param_name] = parse_parameter_value(yaml_value);
  return true;
}

Context::ParameterValue Context::parse_parameter_value(const std::string & value_str)
{
  // Convert to lowercase for case-insensitive comparison
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

bool Context::parse_yaml_file(const std::string & file_path)
{
  // Corresponds to rcl_parse_yaml_file in rcl_yaml_param_parser
  // Simplified implementation using libyaml

  FILE * file = fopen(file_path.c_str(), "r");
  if (!file) {
    return false;
  }

  yaml_parser_t parser;
  yaml_event_t event;

  if (!yaml_parser_initialize(&parser)) {
    fclose(file);
    return false;
  }

  yaml_parser_set_input_file(&parser, file);

  std::string current_node;
  std::string current_param;
  bool in_ros_parameters = false;
  bool expecting_param_name = false;
  bool expecting_param_value = false;

  bool done = false;
  while (!done) {
    if (!yaml_parser_parse(&parser, &event)) {
      break;
    }

    switch (event.type) {
      case YAML_MAPPING_START_EVENT:
        if (!current_node.empty() && current_param == "ros__parameters") {
          in_ros_parameters = true;
          expecting_param_name = true;
        }
        break;

      case YAML_MAPPING_END_EVENT:
        if (in_ros_parameters) {
          in_ros_parameters = false;
          current_node.clear();
        }
        break;

      case YAML_SCALAR_EVENT: {
        std::string value(reinterpret_cast<const char *>(event.data.scalar.value));

        if (current_node.empty()) {
          // This is a node name
          current_node = value;
          expecting_param_name = false;
        } else if (!in_ros_parameters && value == "ros__parameters") {
          current_param = value;
        } else if (in_ros_parameters) {
          if (expecting_param_name) {
            current_param = value;
            expecting_param_value = true;
            expecting_param_name = false;
          } else if (expecting_param_value) {
            // Store parameter
            parameters_by_node_[current_node][current_param] = parse_parameter_value(value);
            expecting_param_value = false;
            expecting_param_name = true;
          }
        }
      } break;

      case YAML_STREAM_END_EVENT:
        done = true;
        break;

      default:
        break;
    }

    yaml_event_delete(&event);
  }

  yaml_parser_delete(&parser);
  fclose(file);
  return true;
}

std::map<std::string, Context::ParameterValue> Context::get_param_overrides(
  const std::string & node_fqn) const
{
  // Corresponds to rcl_arguments_get_param_overrides in rcl/src/rcl/arguments.c
  std::map<std::string, ParameterValue> result;

  // Start with node-specific parameters from YAML files
  auto node_it = parameters_by_node_.find(node_fqn);
  if (node_it != parameters_by_node_.end()) {
    result = node_it->second;
  }

  // Apply global parameter overrides (from -p flags)
  // These override YAML file parameters
  for (const auto & [name, value] : global_parameter_overrides_) {
    result[name] = value;
  }

  return result;
}

void init(int argc, char const * const * argv)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  g_context.init(argc, argv);
}

}  // namespace agnocast

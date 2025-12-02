#include "agnocast/agnocast_context.hpp"

#include <yaml.h>

#include <charconv>

namespace agnocast
{

Context & Context::instance()
{
  // Singleton pattern using static local variable (thread-safe in C++11+)
  // Corresponds to rclcpp::contexts::get_global_default_context()
  static Context context;
  return context;
}

void Context::init(int argc, char * argv[])
{
  // Corresponds to rcl_parse_arguments in rcl/src/rcl/arguments.c
  if (initialized_) {
    return;
  }

  bool parsing_ros_args = false;

  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];

    if (parsing_ros_args) {
      // Inside --ros-args scope: explicit flags required

      // Ignore ROS specific arguments flag (already inside)
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
        std::string param_arg = argv[++i];
        parse_param_rule(param_arg);  // Parse immediately
        continue;
      }

      // Attempt to parse argument as remap rule flag
      if ((arg == RCL_REMAP_FLAG || arg == RCL_SHORT_REMAP_FLAG) && i + 1 < argc) {
        std::string remap_arg = argv[++i];
        parse_remap_rule(remap_arg);  // Parse immediately
        continue;
      }

      // Attempt to parse argument as parameter file rule
      if (arg == RCL_PARAM_FILE_FLAG && i + 1 < argc) {
        std::string file_path = argv[++i];
        parse_yaml_file(file_path);
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

  initialized_ = true;
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
  if (value_str == "true" || value_str == "True" || value_str == "TRUE") {
    return rclcpp::ParameterValue(true);
  }
  if (value_str == "false" || value_str == "False" || value_str == "FALSE") {
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

void init(int argc, char * argv[])
{
  // Corresponds to rclcpp::init()
  // Initializes the global context with command-line arguments
  Context::instance().init(argc, argv);
}

}  // namespace agnocast

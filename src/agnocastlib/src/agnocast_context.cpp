#include "agnocast/agnocast_context.hpp"

#include <yaml.h>

namespace agnocast
{

Context g_context;
std::mutex g_context_mtx;

void Context::init(int argc, char * argv[])
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

  for (size_t i = 1; i < args.size(); ++i) {
    const std::string & arg = args[i];

    if (parsing_ros_args) {
      // Inside --ros-args scope: explicit flags required

      // Ignore ROS specific arguments flag (already inside)
      if (arg == AGNOCAST_ROS_ARGS_FLAG) {
        continue;
      }

      // Check for ROS specific arguments explicit end token
      if (arg == AGNOCAST_ROS_ARGS_EXPLICIT_END_TOKEN) {
        parsing_ros_args = false;
        continue;
      }

      // Attempt to parse argument as parameter override flag
      if ((arg == AGNOCAST_PARAM_FLAG || arg == AGNOCAST_SHORT_PARAM_FLAG) && i + 1 < args.size()) {
        parse_param_rule(args[++i]);  // Parse immediately
        continue;
      }

      // Attempt to parse argument as remap rule flag
      if ((arg == AGNOCAST_REMAP_FLAG || arg == AGNOCAST_SHORT_REMAP_FLAG) && i + 1 < args.size()) {
        parse_remap_rule(args[++i]);  // Parse immediately
        continue;
      }

      // Attempt to parse argument as parameter file rule
      if (arg == AGNOCAST_PARAM_FILE_FLAG && i + 1 < args.size()) {
        parse_yaml_file(args[++i]);
        continue;
      }

      // Unknown ROS specific argument - skip it
      // In RCL this would be stored in unparsed_ros_args

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

bool Context::parse_yaml_file(const std::string & file_path)
{
  // Corresponds to rcl_parse_yaml_file in rcl_yaml_param_parser

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

void init(int argc, char * argv[])
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  g_context.init(argc, argv);
}

}  // namespace agnocast

#include "agnocast/agnocast_node.hpp"

#include <algorithm>
#include <cctype>
#include <sstream>

namespace agnocast
{

Node::Node(
  int argc, char * argv[], const std::string & default_node_name,
  const std::string & default_namespace)
: node_name_(default_node_name), namespace_(default_namespace)
{
  // Normalize namespace (ensure it starts with '/' or is empty)
  if (!namespace_.empty() && namespace_[0] != '/') {
    namespace_ = "/" + namespace_;
  }

  parse_ros_args(argc, argv);
}

Node::Node(const std::string & node_name, const std::string & namespace_)
: node_name_(node_name), namespace_(namespace_)
{
  // Normalize namespace
  if (!namespace_.empty() && namespace_[0] != '/') {
    namespace_ = "/" + namespace_;
  }
}

std::string Node::get_fully_qualified_name() const
{
  if (namespace_.empty() || namespace_ == "/") {
    return "/" + node_name_;
  }
  return namespace_ + "/" + node_name_;
}

std::string Node::resolve_topic_name(const std::string & topic_name) const
{
  if (topic_name.empty()) {
    return topic_name;
  }

  std::string resolved = topic_name;

  // Handle private topic name (starts with '~')
  if (topic_name[0] == '~') {
    resolved = get_fully_qualified_name() + "/" + topic_name.substr(1);
  }
  // Handle relative topic name (doesn't start with '/')
  else if (topic_name[0] != '/') {
    if (namespace_.empty() || namespace_ == "/") {
      resolved = "/" + topic_name;
    } else {
      resolved = namespace_ + "/" + topic_name;
    }
  }
  // Absolute topic name - use as-is
  // else: resolved = topic_name

  // Apply remapping
  resolved = apply_remapping(resolved);

  return resolved;
}

std::string Node::apply_remapping(const std::string & topic_name) const
{
  auto it = topic_remappings_.find(topic_name);
  if (it != topic_remappings_.end()) {
    return it->second;
  }
  return topic_name;
}

void Node::parse_ros_args(int argc, char * argv[])
{
  bool in_ros_args = false;

  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];

    if (arg == "--ros-args") {
      in_ros_args = true;
      continue;
    }

    if (!in_ros_args) {
      continue;
    }

    // End of ROS args
    if (arg == "--") {
      break;
    }

    // Parse remapping: -r name:=value
    if (arg == "-r" && i + 1 < argc) {
      std::string remap_arg = argv[++i];
      size_t delim_pos = remap_arg.find(":=");

      if (delim_pos != std::string::npos) {
        std::string from = remap_arg.substr(0, delim_pos);
        std::string to = remap_arg.substr(delim_pos + 2);

        // Special remappings
        if (from == "__ns") {
          namespace_ = to;
          // Normalize namespace
          if (!namespace_.empty() && namespace_[0] != '/') {
            namespace_ = "/" + namespace_;
          }
        } else if (from == "__node") {
          node_name_ = to;
        } else {
          // Topic remapping
          topic_remappings_[from] = to;
        }
      }
      continue;
    }

    // Parse parameter: -p name:=value
    if (arg == "-p" && i + 1 < argc) {
      std::string param_arg = argv[++i];
      size_t delim_pos = param_arg.find(":=");

      if (delim_pos != std::string::npos) {
        std::string name = param_arg.substr(0, delim_pos);
        std::string value_str = param_arg.substr(delim_pos + 2);

        parameters_[name] = parse_parameter_value(value_str);
      }
      continue;
    }
  }
}

Node::ParameterValue Node::parse_parameter_value(const std::string & value_str) const
{
  // Try to parse as bool
  if (value_str == "true" || value_str == "True" || value_str == "TRUE") {
    return true;
  }
  if (value_str == "false" || value_str == "False" || value_str == "FALSE") {
    return false;
  }

  // Try to parse as integer
  try {
    size_t pos = 0;
    int64_t int_value = std::stoll(value_str, &pos);
    if (pos == value_str.length()) {
      return int_value;
    }
  } catch (...) {
  }

  // Try to parse as double
  try {
    size_t pos = 0;
    double double_value = std::stod(value_str, &pos);
    if (pos == value_str.length()) {
      return double_value;
    }
  } catch (...) {
  }

  // Default to string
  return value_str;
}

bool Node::get_parameter(const std::string & name, bool & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<bool>(&it->second)) {
    value = *v;
    return true;
  }
  return false;
}

bool Node::get_parameter(const std::string & name, int64_t & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<int64_t>(&it->second)) {
    value = *v;
    return true;
  }
  return false;
}

bool Node::get_parameter(const std::string & name, double & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<double>(&it->second)) {
    value = *v;
    return true;
  }
  return false;
}

bool Node::get_parameter(const std::string & name, std::string & value) const
{
  auto it = parameters_.find(name);
  if (it == parameters_.end()) {
    return false;
  }

  if (auto * v = std::get_if<std::string>(&it->second)) {
    value = *v;
    return true;
  }
  return false;
}

}  // namespace agnocast

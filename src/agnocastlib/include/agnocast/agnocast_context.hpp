#pragma once

#include <map>
#include <string>
#include <variant>
#include <vector>

#include "agnocast/agnocast_node.hpp"

namespace agnocast
{

// Command-line argument flags (corresponds to rcl/include/rcl/arguments.h)
/// The command-line flag that delineates the start of ROS arguments.
#define AGNOCAST_ROS_ARGS_FLAG "--ros-args"

/// The token that delineates the explicit end of ROS arguments.
#define AGNOCAST_ROS_ARGS_EXPLICIT_END_TOKEN "--"

/// The ROS flag that precedes the setting of a ROS parameter.
#define AGNOCAST_PARAM_FLAG "--param"

/// The short version of the ROS flag that precedes the setting of a ROS parameter.
#define AGNOCAST_SHORT_PARAM_FLAG "-p"

/// The ROS flag that precedes a path to a file containing ROS parameters.
#define AGNOCAST_PARAM_FILE_FLAG "--params-file"

/// The ROS flag that precedes a ROS remapping rule.
#define AGNOCAST_REMAP_FLAG "--remap"

/// The short version of the ROS flag that precedes a ROS remapping rule.
#define AGNOCAST_SHORT_REMAP_FLAG "-r"

class GlobalContext
{
public:
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  static GlobalContext & instance();
  void init(int argc, char * argv[]);
  bool is_initialized() const { return initialized_; }
  const std::vector<RemapRule> & get_remap_rules() const { return remap_rules_; }

  /// Get parameter overrides for a specific node
  /// Corresponds to rcl_arguments_get_param_overrides in rcl/src/rcl/arguments.c
  std::map<std::string, ParameterValue> get_param_overrides(
    const std::string & node_fqn) const;

  /// Deprecated: Use get_param_overrides() instead
  const std::map<std::string, ParameterValue> & get_parameter_overrides() const
  {
    return global_parameter_overrides_;
  }

private:
  GlobalContext() = default;
  ~GlobalContext() = default;

  // Prevent copying and moving
  GlobalContext(const GlobalContext &) = delete;
  GlobalContext & operator=(const GlobalContext &) = delete;
  GlobalContext(GlobalContext &&) = delete;
  GlobalContext & operator=(GlobalContext &&) = delete;

  bool parse_remap_rule(const std::string & arg);
  bool parse_param_rule(const std::string & arg);
  bool parse_yaml_file(const std::string & file_path);

  ParameterValue parse_parameter_value(const std::string & value_str);

  bool initialized_ = false;
  std::vector<RemapRule> remap_rules_;

  /// Parameters organized by node name (corresponds to rcl_params_t)
  /// Map: node_fqn -> (param_name -> param_value)
  std::map<std::string, std::map<std::string, ParameterValue>> parameters_by_node_;

  /// Global parameter overrides (applied to all nodes, from -p flags without node prefix)
  std::map<std::string, ParameterValue> global_parameter_overrides_;
};

void init(int argc, char * argv[]);

}  // namespace agnocast

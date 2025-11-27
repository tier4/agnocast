#pragma once

#include <map>
#include <mutex>
#include <string>
#include <variant>
#include <vector>

namespace agnocast
{

// Remap types (corresponds to rcl/src/rcl/remap.c)
enum class RemapType
{
  NODENAME,
  NAMESPACE,
  TOPIC
};

struct RemapRule
{
  RemapType type;
  std::string match;
  std::string replacement;
};

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

class Context
{
public:
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  void init(int argc, char * argv[]);
  bool is_initialized() const { return initialized_; }
  const std::vector<RemapRule> & get_remap_rules() const { return remap_rules_; }

private:
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

extern Context g_context;
extern std::mutex g_context_mtx;

void init(int argc, char * argv[]);

}  // namespace agnocast

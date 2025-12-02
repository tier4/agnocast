#pragma once

#include <rcl/arguments.h>

#include <map>
#include <mutex>
#include <string>
#include <variant>
#include <vector>

namespace agnocast
{

/// Remap rule types (corresponds to rcl_remap_type_t in rcl/include/rcl/remap.h)
enum class RemapType {
  NODENAME,   ///< Node name remapping (__node or __name)
  NAMESPACE,  ///< Namespace remapping (__ns)
  TOPIC       ///< Topic name remapping
};

/// Structure to hold a single remapping rule
struct RemapRule
{
  RemapType type;
  std::string match;        ///< Original name to match
  std::string replacement;  ///< Replacement name
};

class Context
{
public:
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  static Context & instance();
  void init(int argc, char * argv[]);
  bool is_initialized() const { return initialized_; }
  const std::vector<RemapRule> & get_remap_rules() const { return remap_rules_; }

  /// Get parameter overrides for a specific node
  /// Corresponds to rcl_arguments_get_param_overrides in rcl/src/rcl/arguments.c
  std::map<std::string, ParameterValue> get_param_overrides(const std::string & node_fqn) const;

  /// Deprecated: Use get_param_overrides() instead
  const std::map<std::string, ParameterValue> & get_parameter_overrides() const
  {
    return global_parameter_overrides_;
  }

private:
  Context() = default;
  ~Context() = default;

  // Prevent copying and moving
  Context(const Context &) = delete;
  Context & operator=(const Context &) = delete;
  Context(Context &&) = delete;
  Context & operator=(Context &&) = delete;

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

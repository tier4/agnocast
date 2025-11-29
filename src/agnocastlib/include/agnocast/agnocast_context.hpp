#pragma once

#include <map>
#include <mutex>
#include <string>
#include <variant>
#include <vector>

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

main
class Context
{
  struct CommandLineParams
  {
    std::string node_name;
  };

public:
  CommandLineParams command_line_params;
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  void init(int argc, char const * const * argv);
  bool is_initialized() const { return initialized_; }

private:
  bool initialized_ = false;
  bool parse_param_rule(const std::string & arg);
  ParameterValue parse_parameter_value(const std::string & value_str);

  std::map<std::string, ParameterValue> global_parameter_overrides_;
};

extern Context g_context;
extern std::mutex g_context_mtx;

void init(int argc, char const * const * argv);

}  // namespace agnocast

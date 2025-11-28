#pragma once

#include <map>
#include <mutex>
#include <string>
#include <variant>
#include <vector>

namespace agnocast
{

// Remap types (corresponds to rcl/src/rcl/remap.c)
enum class RemapType { NODENAME, NAMESPACE, TOPIC };

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
  struct CommandLineParams
  {
    std::string node_name;
  };

public:
  CommandLineParams command_line_params;

  void init(int argc, char * argv[]);
  bool is_initialized() const { return initialized_; }

private:
  bool initialized_ = false;
};

extern Context g_context;
extern std::mutex g_context_mtx;

void init(int argc, char * argv[]);

}  // namespace agnocast

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

#include "agnocast/agnocast_context.hpp"

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

  std::string node_name;
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

      if (arg == "-r" && i + 1 < argc) {
        std::string remap{args[i + 1]};
        const std::string prefix = "__node:=";

        if (remap.compare(0, prefix.size(), prefix) == 0) {
          node_name = remap.substr(prefix.size());

          {
            std::lock_guard<std::mutex> lock(g_context_mtx);
            g_context.command_line_params.node_name = node_name;
          }

          break;
        }
      }

      // TODO: Parse other ROS specific arguments here.

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

void init(int argc, char * argv[])
{
  g_context.init(argc, argv);
}

}  // namespace agnocast

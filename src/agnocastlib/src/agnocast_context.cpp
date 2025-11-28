#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Context g_context;
std::mutex g_context_mtx;

void init(int argc, char const * const * argv)
{
  std::string node_name;
  // Copy argv into a safe container to avoid pointer arithmetic
  std::vector<std::string> args;
  args.reserve(static_cast<size_t>(argc));
  for (int i = 0; i < argc; ++i) {
    args.emplace_back(argv[i]);  // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
  }

  bool in_ros_args = false;
  for (int i = 0; i < argc; i++) {
    std::string arg_str = args[i];

    if (!in_ros_args) {
      if (arg_str == "--ros-args") {
        in_ros_args = true;
      }

      continue;
    }

    if (arg_str == "-r" && i + 1 < argc) {
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
  }
}

}  // namespace agnocast

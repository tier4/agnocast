#include "agnocast/agnocast_context.hpp"

#include <memory>

namespace agnocast
{

extern Context g_context;
extern std::mutex g_context_mtx;

inline std::string query_node_name()
{
  std::string node_name;
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    node_name = g_context.command_line_params.node_name;
  }
  return node_name;
}

}  // namespace agnocast

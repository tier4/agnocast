#include "agnocast/agnocast_context.hpp"

namespace agnocast
{

Context g_context;
std::mutex g_context_mtx;

void Context::init(int argc, char const * const * argv)
{
  if (initialized_) {
    return;
  }

  parsed_arguments_ = parse_arguments(argc, argv);
  initialized_ = true;
}

void init(int argc, char const * const * argv)
{
  std::lock_guard<std::mutex> lock(g_context_mtx);
  g_context.init(argc, argv);
}

}  // namespace agnocast

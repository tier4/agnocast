#pragma once

#include <rcl/arguments.h>

#include <mutex>
#include <string>
#include <vector>

namespace agnocast
{

class Context
{
  struct CommandLineParams
  {
    std::string node_name;
  };

public:
  CommandLineParams command_line_params;

  void init(int argc, char const * const * argv);
  bool is_initialized() const { return initialized_; }

private:
  bool initialized_ = false;
};

extern Context g_context;
extern std::mutex g_context_mtx;

void init(int argc, char const * const * argv);

}  // namespace agnocast

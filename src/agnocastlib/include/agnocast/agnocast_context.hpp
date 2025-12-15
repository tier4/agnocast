#pragma once

#include "agnocast/agnocast_arguments.hpp"

#include <mutex>

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
  std::vector<RemapRule> get_remap_rules() const { return parsed_arguments_.remap_rules; }

private:
  bool initialized_ = false;
  ParsedArguments parsed_arguments_;
};

extern Context g_context;
extern std::mutex g_context_mtx;

void init(int argc, char const * const * argv);

}  // namespace agnocast

#pragma once

#include <rclcpp/parameter_value.hpp>

#include <rcl/arguments.h>

#include <map>
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
  using ParameterValue = rclcpp::ParameterValue;

  CommandLineParams command_line_params;

  void init(int argc, char const * const * argv);
  bool is_initialized() const { return initialized_; }

private:
  bool parse_param_rule(const std::string & arg);
  ParameterValue parse_parameter_value(const std::string & value_str);

  bool initialized_ = false;

  std::map<std::string, ParameterValue> global_parameter_overrides_;
};

extern Context g_context;
extern std::mutex g_context_mtx;

void init(int argc, char const * const * argv);

}  // namespace agnocast

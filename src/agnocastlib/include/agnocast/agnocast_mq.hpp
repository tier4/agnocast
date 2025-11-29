#pragma once

#include <cstddef>
#include <cstdint>

namespace agnocast
{

inline constexpr size_t SHARED_LIB_PATH_BUFFER_SIZE = 4096;  // Linux PATH_MAX is 4096
inline constexpr size_t TOPIC_NAME_BUFFER_SIZE = 256;
inline constexpr size_t SYMBOL_NAME_BUFFER_SIZE = 256;

struct MqMsgAgnocast
{
};

struct MqMsgROS2Publish
{
  bool should_terminate;
};

struct MqMsgBridge
{
  uintptr_t fn_ptr;
  char shared_lib_path[SHARED_LIB_PATH_BUFFER_SIZE];
  char symbol_name[SYMBOL_NAME_BUFFER_SIZE];
  char topic_name[TOPIC_NAME_BUFFER_SIZE];
};

}  // namespace agnocast

#pragma once

#include "agnocast/agnocast_ioctl.hpp"

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

enum class BridgeDirection : uint32_t { ROS2_TO_AGNOCAST = 0, AGNOCAST_TO_ROS2 = 1 };

struct BridgeFactoryInfo
{
  char shared_lib_path[SHARED_LIB_PATH_BUFFER_SIZE];
  char symbol_name[SYMBOL_NAME_BUFFER_SIZE];
  uintptr_t fn_offset;
  uintptr_t fn_offset_reverse;
};

struct BridgeTargetInfo
{
  char topic_name[TOPIC_NAME_BUFFER_SIZE];
  topic_local_id_t target_id;
};

struct MqMsgBridge
{
  BridgeFactoryInfo factory;
  BridgeTargetInfo target;
  BridgeDirection direction;
};

}  // namespace agnocast

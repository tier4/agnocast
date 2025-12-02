#pragma once

#include "agnocast/agnocast_ioctl.hpp"

#include <cstddef>
#include <cstdint>

inline constexpr size_t MAX_SHARED_LIB_PATH_LEN = 4096;  // Linux PATH_MAX is 4096
inline constexpr size_t MAX_SYMBOL_NAME_LEN = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
};

enum class BridgeDirection : uint32_t { ROS2_TO_AGNOCAST = 0, AGNOCAST_TO_ROS2 = 1 };

struct BridgeFactoryInfo
{
  char shared_lib_path[MAX_SHARED_LIB_PATH_LEN];
  char symbol_name[MAX_SYMBOL_NAME_LEN];
  uintptr_t fn_offset;
  uintptr_t fn_offset_reverse;
};

struct BridgeTargetInfo
{
  char topic_name[MAX_TOPIC_NAME_LEN];
  topic_local_id_t target_id;
};

struct MqMsgBridge
{
  BridgeFactoryInfo factory;
  BridgeTargetInfo target;
  BridgeDirection direction;
};

}  // namespace agnocast
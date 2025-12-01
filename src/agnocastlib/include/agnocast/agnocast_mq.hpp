#pragma once

#include "agnocast/agnocast_ioctl.hpp"

#include <cstddef>
#include <cstdint>

inline constexpr size_t MAX_NAME_LENGTH = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
};

enum class BridgeDirection : uint32_t { ROS2_TO_AGNOCAST = 0, AGNOCAST_TO_ROS2 = 1 };

struct BridgeFactoryInfo
{
  char shared_lib_path[MAX_NAME_LENGTH];
  char symbol_name[MAX_NAME_LENGTH];
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
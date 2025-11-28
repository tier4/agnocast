#pragma once

#include <cstddef>
#include <cstdint>

inline constexpr size_t MAX_NAME_LENGTH = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
};

enum class BridgeDirection : uint32_t { ROS2_TO_AGNOCAST = 0, AGNOCAST_TO_ROS2 = 1 };

enum class BridgeCommand : uint32_t {
  CREATE_BRIDGE = 0,
  REMOVE_BRIDGE = 1,
  DELEGATE_CREATE = 2  // <--- NEW: 既存オーナーへの作成委譲用
};

struct QoSFlat
{
  uint32_t depth;
  uint8_t history;
  uint8_t reliability;
  uint8_t durability;
};

struct BridgeArgs
{
  char topic_name[MAX_NAME_LENGTH];
  QoSFlat qos;
};

struct MqMsgBridge
{
  char shared_lib_path[MAX_NAME_LENGTH];
  char symbol_name[MAX_NAME_LENGTH];
  uintptr_t fn_ptr;
  uintptr_t fn_ptr_reverse;  // <--- NEW: 逆方向の生成関数ポインタ(キャッシュ用)
  BridgeDirection direction;
  BridgeCommand command;
  BridgeArgs args;
};

}  // namespace agnocast
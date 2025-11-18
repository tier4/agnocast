#pragma once

#include <cstddef>
#include <cstdint>

inline constexpr size_t MAX_NAME_LENGTH = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
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
  BridgeArgs args;
};

}  // namespace agnocast

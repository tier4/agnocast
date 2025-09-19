#pragma once

constexpr size_t kMaxNameLen = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
};

struct MqMsgROS2Publish
{
  bool should_terminate;
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
  char topic_name[kMaxNameLen];
  QoSFlat qos;
};

struct MqMsgBridge
{
  char shared_lib_path[kMaxNameLen];
  char symbol_name[kMaxNameLen];
  uintptr_t fn_ptr;
  BridgeArgs args;
};

}  // namespace agnocast
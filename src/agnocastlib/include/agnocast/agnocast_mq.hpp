#pragma once

inline constexpr size_t MAX_NAME_LENGTH = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
};

struct MqMsgROS2Publish
{
  bool should_terminate;
};

struct BridgeRequest
{
  char topic_name[MAX_NAME_LENGTH];
  char message_type[MAX_NAME_LENGTH];
};

}  // namespace agnocast

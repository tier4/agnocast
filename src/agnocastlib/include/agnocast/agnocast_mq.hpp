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

struct BridgeRequest
{
  char topic_name[kMaxNameLen];
  char message_type[kMaxNameLen];
};

}  // namespace agnocast

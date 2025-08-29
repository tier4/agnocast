#pragma once

namespace agnocast
{

struct MqMsgAgnocast
{
};

struct MqMsgROS2Publish
{
  bool should_terminate;
};

struct MqMsgTopicInfo
{
  pid_t pid;
  char topic_name[256];
};

}  // namespace agnocast

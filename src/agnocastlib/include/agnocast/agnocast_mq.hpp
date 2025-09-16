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

struct MqMsgBridge
{
  std::string shared_lib_path;
  void * fn_ptr;
};

}  // namespace agnocast
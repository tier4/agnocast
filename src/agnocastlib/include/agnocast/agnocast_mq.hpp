#pragma once

#include "agnocast/agnocast_bridge_types.hpp"

inline constexpr size_t MAX_NAME_LENGTH = 256;

namespace agnocast
{

struct MqMsgAgnocast
{
};

struct BridgeRequest
{
  char topic_name[MAX_NAME_LENGTH];
  char message_type[MAX_NAME_LENGTH];
  BridgeDirection direction;
};

}  // namespace agnocast

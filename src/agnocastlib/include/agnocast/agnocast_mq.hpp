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

enum class BridgeDirection { ROS2_TO_AGNOCAST, AGNOCAST_TO_ROS2, BIDIRECTIONAL };

struct BridgeRequest
{
  char topic_name[MAX_NAME_LENGTH];
  char message_type[MAX_NAME_LENGTH];
  BridgeDirection direction;  // ★ 方向を示すフィールドを追加
};

}  // namespace agnocast

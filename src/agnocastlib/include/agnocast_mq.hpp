#pragma once

#include <cstdint>

namespace agnocast
{

struct MqMsgNewPublisher
{
  uint32_t publisher_pid;
  uint64_t shm_addr;
};

struct MqMsgAgnocast
{
  uint32_t publisher_pid;
  uint64_t timestamp;
};

}  // namespace agnocast

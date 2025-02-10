#pragma once

#include <cstdint>

namespace agnocast
{

struct MqMsgNewPublisher
{
  pid_t publisher_pid;
  uint64_t shm_addr;
  uint64_t shm_size;
};

struct MqMsgAgnocast
{
};

}  // namespace agnocast

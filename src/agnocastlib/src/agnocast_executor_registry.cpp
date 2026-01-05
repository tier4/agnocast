#include "agnocast/agnocast_executor_registry.hpp"

#include <sys/eventfd.h>
#include <unistd.h>

#include <cstdint>

namespace agnocast
{

void ExecutorRegistry::notify_all()
{
  std::lock_guard<std::mutex> lock(mutex_);
  for (int fd : notify_fds_) {
    uint64_t val = 1;
    // Write to eventfd to wake up the executor
    // Ignore errors since the executor might have been destroyed
    (void)write(fd, &val, sizeof(val));
  }
}

}  // namespace agnocast

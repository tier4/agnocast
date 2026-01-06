#include "agnocast/agnocast_executor_registry.hpp"

#include <unistd.h>

#include <cstdint>
#include <mutex>
#include <set>

namespace agnocast
{

namespace
{
std::mutex executor_notify_fds_mtx;
std::set<int> executor_notify_fds;
}  // namespace

void register_executor_notify_fd(int notify_fd)
{
  std::lock_guard<std::mutex> lock(executor_notify_fds_mtx);
  executor_notify_fds.insert(notify_fd);
}

void unregister_executor_notify_fd(int notify_fd)
{
  std::lock_guard<std::mutex> lock(executor_notify_fds_mtx);
  executor_notify_fds.erase(notify_fd);
}

void notify_executors()
{
  std::lock_guard<std::mutex> lock(executor_notify_fds_mtx);
  for (int fd : executor_notify_fds) {
    uint64_t val = 1;
    if (write(fd, &val, sizeof(val)) < 0) {
      // Write to eventfd should not fail, but ignore if it does
    }
  }
}

}  // namespace agnocast

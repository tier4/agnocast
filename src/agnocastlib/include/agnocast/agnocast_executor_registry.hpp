#pragma once

#include <mutex>
#include <set>

namespace agnocast
{

// Global registry of executor notify file descriptors.
// When a new callback or timer is registered, all executors are notified
// via their eventfd so they can register the new entity to their epoll.
class ExecutorRegistry
{
public:
  static ExecutorRegistry & get_instance()
  {
    static ExecutorRegistry instance;
    return instance;
  }

  // Register an executor's notify_fd to the registry.
  // Called from executor constructor.
  void register_executor(int notify_fd)
  {
    std::lock_guard<std::mutex> lock(mutex_);
    notify_fds_.insert(notify_fd);
  }

  // Unregister an executor's notify_fd from the registry.
  // Called from executor destructor.
  void unregister_executor(int notify_fd)
  {
    std::lock_guard<std::mutex> lock(mutex_);
    notify_fds_.erase(notify_fd);
  }

  // Notify all registered executors that a new callback/timer has been registered.
  // Called from register_callback() and register_timer().
  void notify_all();

private:
  ExecutorRegistry() = default;
  ~ExecutorRegistry() = default;

  ExecutorRegistry(const ExecutorRegistry &) = delete;
  ExecutorRegistry & operator=(const ExecutorRegistry &) = delete;

  std::mutex mutex_;
  std::set<int> notify_fds_;
};

// Convenience function to notify all executors
inline void notify_executors()
{
  ExecutorRegistry::get_instance().notify_all();
}

}  // namespace agnocast

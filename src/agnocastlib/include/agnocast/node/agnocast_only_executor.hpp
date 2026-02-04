#pragma once

#include "rclcpp/callback_group.hpp"

#include <atomic>
#include <memory>
#include <mutex>
#include <set>
#include <vector>

namespace agnocast
{

struct AgnocastExecutable;
class Node;

class AgnocastOnlyExecutor
{
protected:
  std::atomic_bool spinning_;
  int epoll_fd_;
  int shutdown_event_fd_;
  pid_t my_pid_;

  std::mutex ready_agnocast_executables_mutex_;
  std::vector<AgnocastExecutable> ready_agnocast_executables_;
  std::set<rclcpp::CallbackGroup::SharedPtr> added_callback_groups_;

  bool get_next_agnocast_executable(
    AgnocastExecutable & agnocast_executable, const int timeout_ms, bool & shutdown_detected);
  bool get_next_ready_agnocast_executable(AgnocastExecutable & agnocast_executable);
  void execute_agnocast_executable(AgnocastExecutable & agnocast_executable);
  bool validate_callback_group(const rclcpp::CallbackGroup::SharedPtr & group) const;

public:
  explicit AgnocastOnlyExecutor();

  virtual ~AgnocastOnlyExecutor();

  virtual void spin() = 0;
  void cancel();

  void add_node(const std::shared_ptr<agnocast::Node> & node);
  void add_callback_group(const rclcpp::CallbackGroup::SharedPtr & callback_group);
};

}  // namespace agnocast

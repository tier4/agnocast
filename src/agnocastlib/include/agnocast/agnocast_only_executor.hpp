#pragma once

#include "agnocast/agnocast.hpp"

namespace agnocast
{

class AgnocastOnlyExecutor
{
  std::atomic_bool spinning_;
  int epoll_fd_;
  pid_t my_pid_;
  const int next_exec_timeout_ms_;

  std::mutex ready_agnocast_executables_mutex_;
  std::vector<AgnocastExecutable> ready_agnocast_executables_;

  bool get_next_agnocast_executable(AgnocastExecutable & agnocast_executable, const int timeout_ms);
  bool get_next_ready_agnocast_executable(AgnocastExecutable & agnocast_executable);
  void execute_agnocast_executable(AgnocastExecutable & agnocast_executable);

public:
  explicit AgnocastOnlyExecutor(int next_exec_timeout_ms = 50);

  virtual ~AgnocastOnlyExecutor();

  void spin();

  void add_node(const agnocast::Node::SharedPtr & node);
};

}  // namespace agnocast
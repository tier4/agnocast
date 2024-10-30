#pragma once

#include "agnocast_topic_info.hpp"
#include "rclcpp/rclcpp.hpp"

#include <queue>

namespace agnocast
{

struct AgnocastExecutables
{
  std::queue<std::shared_ptr<std::function<void()>>> callable_queue;
};

class SingleThreadedAgnocastExecutor : public rclcpp::Executor
{
  int epoll_fd_;
  pid_t my_pid_;
  rclcpp::Node::SharedPtr node_;

  RCLCPP_DISABLE_COPY(SingleThreadedAgnocastExecutor)

  bool get_next_agnocast_executables(AgnocastExecutables & agnocast_executables, int timeout_ms);
  void execute_agnocast_executables(AgnocastExecutables & agnocast_executables);

public:
  RCLCPP_PUBLIC
  explicit SingleThreadedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions());

  RCLCPP_PUBLIC
  virtual ~SingleThreadedAgnocastExecutor();

  RCLCPP_PUBLIC
  void spin() override;

  void add_node(rclcpp::Node::SharedPtr node, bool notify = true) override;
};

}  // namespace agnocast

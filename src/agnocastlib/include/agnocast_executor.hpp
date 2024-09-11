#pragma once

#include "agnocast_topic_info.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

struct AgnocastExecutable
{
  std::function<void()> callable;
};

class SingleThreadedAgnocastExecutor : public rclcpp::Executor
{
  int epoll_fd_;
  pid_t my_pid_;
  rclcpp::Node::SharedPtr node_;

  RCLCPP_DISABLE_COPY(SingleThreadedAgnocastExecutor)

  bool get_next_agnocast_executable(AgnocastExecutable & agnocast_executable, int timeout_ms);
  void execute_agnocast_executable(const AgnocastExecutable & agnocast_executable);

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

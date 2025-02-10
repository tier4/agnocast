#pragma once

#include "agnocast_callback_info.hpp"
#include "rclcpp/rclcpp.hpp"

#include <queue>

namespace agnocast
{

void map_read_only_area(const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size);

struct AgnocastExecutables
{
  std::queue<std::shared_ptr<std::function<void()>>> callable_queue;
  rclcpp::CallbackGroup::SharedPtr callback_group{nullptr};
};

class AgnocastExecutor : public rclcpp::Executor
{
  // prevent objects from being destructed by keeping reference count
  std::vector<rclcpp::Node::SharedPtr> nodes_;

  std::chrono::nanoseconds agnocast_callback_group_wait_time_;

protected:
  int epoll_fd_;
  pid_t my_pid_;

  void prepare_epoll();
  bool get_next_agnocast_executables(
    AgnocastExecutables & agnocast_executables, const int timeout_ms) const;
  void execute_agnocast_executables(AgnocastExecutables & agnocast_executables);

public:
  RCLCPP_PUBLIC
  explicit AgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions(),
    std::chrono::nanoseconds agnocast_callback_group_wait_time =
      std::chrono::nanoseconds(10 * 1000 * 1000));

  RCLCPP_PUBLIC
  virtual ~AgnocastExecutor();

  void add_node(rclcpp::Node::SharedPtr node, bool notify = true) override;

  virtual void spin() = 0;
};

}  // namespace agnocast

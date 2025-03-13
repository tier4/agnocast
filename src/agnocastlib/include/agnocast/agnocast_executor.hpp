#pragma once

#include "agnocast/agnocast_callback_info.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

void map_read_only_area(const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size);

struct AgnocastExecutable
{
  std::shared_ptr<std::function<void()>> callable;
  rclcpp::CallbackGroup::SharedPtr callback_group{nullptr};
};

class AgnocastExecutor : public rclcpp::Executor
{
  // prevent objects from being destructed by keeping reference count
  std::vector<rclcpp::Node::SharedPtr> nodes_;

  std::mutex ready_agnocast_executables_mutex_;
  std::vector<AgnocastExecutable> ready_agnocast_executables_;

  void wait_and_handle_epoll_event(const int timeout_ms);
  bool get_next_ready_agnocast_executable(AgnocastExecutable & agnocast_executable);
  virtual void validate_callback_group(const rclcpp::CallbackGroup::SharedPtr & group) const = 0;

protected:
  int epoll_fd_;
  pid_t my_pid_;
  std::mutex wait_mutex_;

  void prepare_epoll();
  bool get_next_agnocast_executable(AgnocastExecutable & agnocast_executable, const int timeout_ms);
  static void execute_agnocast_executable(AgnocastExecutable & agnocast_executable);

public:
  RCLCPP_PUBLIC
  explicit AgnocastExecutor(const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions());

  RCLCPP_PUBLIC
  virtual ~AgnocastExecutor();

  void add_node(rclcpp::Node::SharedPtr node, bool notify = true) override;

  virtual void spin() = 0;
};

}  // namespace agnocast

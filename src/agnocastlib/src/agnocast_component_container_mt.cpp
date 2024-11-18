#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp_components/component_manager.hpp"

#include <chrono>

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  size_t number_of_ros2_threads = 1;
  size_t number_of_agnocast_threads = 0;
  bool ros2_yield_before_execute = false;
  std::chrono::nanoseconds ros2_next_exec_timeout = std::chrono::nanoseconds(10 * 1000 * 1000);
  std::chrono::nanoseconds agnocast_callback_group_wait_time =
    std::chrono::nanoseconds(10 * 1000 * 1000);

  auto node = std::make_shared<rclcpp_components::ComponentManager>();

  if (node->has_parameter("number_of_ros2_threads")) {
    number_of_ros2_threads = node->get_parameter("number_of_ros2_threads").as_int();
  }

  if (node->has_parameter("number_of_agnocast_threads")) {
    number_of_agnocast_threads = node->get_parameter("number_of_agnocast_threads").as_int();
  }

  if (node->has_parameter("ros2_yield_before_execute")) {
    ros2_yield_before_execute = node->get_parameter("ros2_yield_before_execute").as_bool();
  }

  if (node->has_parameter("ros2_next_exec_timeout_ms")) {
    auto ms = node->get_parameter("ros2_next_exec_timeout_ms").as_int();
    ros2_next_exec_timeout = std::chrono::nanoseconds(ms * 1000 * 1000);
  }

  if (node->has_parameter("agnocast_callback_group_wait_time_ms")) {
    auto ms = node->get_parameter("agnocast_callback_group_wait_time_ms").as_int();
    agnocast_callback_group_wait_time = std::chrono::nanoseconds(ms * 1000 * 1000);
  }

  auto executor = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
    rclcpp::ExecutorOptions{}, number_of_ros2_threads, number_of_agnocast_threads,
    ros2_yield_before_execute, ros2_next_exec_timeout, agnocast_callback_group_wait_time);

  node->set_executor(executor);
  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}

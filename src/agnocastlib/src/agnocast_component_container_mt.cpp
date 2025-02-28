#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp_components/component_manager.hpp"

#include <chrono>

int main(int argc, char * argv[])
{
  using namespace std::chrono;

  rclcpp::init(argc, argv);
  auto node = std::make_shared<rclcpp_components::ComponentManager>();

  const size_t number_of_ros2_threads = (node->has_parameter("number_of_ros2_threads"))
                                          ? node->get_parameter("number_of_ros2_threads").as_int()
                                          : 0;
  const size_t number_of_agnocast_threads =
    (node->has_parameter("number_of_agnocast_threads"))
      ? node->get_parameter("number_of_agnocast_threads").as_int()
      : 0;
  const bool yield_before_execute = (node->has_parameter("yield_before_execute"))
                                      ? node->get_parameter("yield_before_execute").as_bool()
                                      : false;
  const nanoseconds ros2_next_exec_timeout =
    (node->has_parameter("ros2_next_exec_timeout_ms"))
      ? nanoseconds(node->get_parameter("ros2_next_exec_timeout_ms").as_int() * 1000 * 1000)
      : nanoseconds(10 * 1000 * 1000);
  const int agnocast_next_exec_timeout_ms =
    (node->has_parameter("agnocast_next_exec_timeout_ms"))
      ? static_cast<int>(node->get_parameter("agnocast_next_exec_timeout_ms").as_int())
      : 1000;

  auto executor = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
    rclcpp::ExecutorOptions{}, number_of_ros2_threads, number_of_agnocast_threads,
    yield_before_execute, ros2_next_exec_timeout, agnocast_next_exec_timeout_ms);

  node->set_executor(executor);
  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}

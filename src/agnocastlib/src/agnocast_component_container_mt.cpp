#include "agnocast/agnocast.hpp"
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
  const nanoseconds timeout = (node->has_parameter("timeout_ns"))
                                ? nanoseconds(node->get_parameter("timeout_ns").as_int())
                                : nanoseconds(10 * 1000 * 1000);

  auto executor = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
    rclcpp::ExecutorOptions{}, number_of_ros2_threads, number_of_agnocast_threads,
    yield_before_execute, timeout);

  node->set_executor(executor);
  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}

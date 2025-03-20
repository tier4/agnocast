#include "agnocast/agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp_components/component_manager.hpp"

#include <chrono>

int main(int argc, char * argv[])
{
  using namespace std::chrono;

  rclcpp::init(argc, argv);

  rclcpp::NodeOptions options;
  options.allow_undeclared_parameters(true);
  options.automatically_declare_parameters_from_overrides(true);

  std::string node_name = "ComponentManager";
  auto node = std::make_shared<rclcpp_components::ComponentManager>(
    std::weak_ptr<rclcpp::Executor>(), node_name, options);

  const size_t number_of_ros2_threads = node->get_parameter_or("number_of_ros2_threads", 0);
  const size_t number_of_agnocast_threads = node->get_parameter_or("number_of_agnocast_threads", 0);
  const bool yield_before_execute = node->get_parameter_or("yield_before_execute", false);
  const nanoseconds ros2_next_exec_timeout_ns =
    nanoseconds(node->get_parameter_or("ros2_next_exec_timeout_ms", 10) * 1000 * 1000);
  const int agnocast_next_exec_timeout_ms =
    node->get_parameter_or("agnocast_next_exec_timeout_ms", 10);

  auto executor = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
    rclcpp::ExecutorOptions{}, number_of_ros2_threads, number_of_agnocast_threads,
    yield_before_execute, ros2_next_exec_timeout_ns, agnocast_next_exec_timeout_ms);

  node->set_executor(executor);
  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}

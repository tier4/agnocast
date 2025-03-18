#include "agnocast/agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp_components/component_manager.hpp"

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  rclcpp::NodeOptions options;
  options.allow_undeclared_parameters(true);
  options.automatically_declare_parameters_from_overrides(true);
  std::string node_name = "component_manager" + std::to_string(getpid());

  auto node = std::make_shared<rclcpp_components::ComponentManager>(
    std::weak_ptr<rclcpp::Executor>(), node_name, options);

  const int get_next_timeout_ms = node->get_parameter_or("get_next_timeout_ms", 50);

  auto executor = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>(
    rclcpp::ExecutorOptions{}, get_next_timeout_ms);

  node->set_executor(executor);
  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}

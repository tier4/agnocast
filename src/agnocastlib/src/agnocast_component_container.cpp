#include "agnocast/agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp_components/component_manager.hpp"

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);
  auto node = std::make_shared<rclcpp_components::ComponentManager>();

  const int get_next_timeout_ms =
    (node->has_parameter("get_next_timeout_ms"))
      ? static_cast<int>(node->get_parameter("get_next_timeout_ms").as_int())
      : 50;

  auto executor = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>(
    rclcpp::ExecutorOptions{}, get_next_timeout_ms);

  node->set_executor(executor);
  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}

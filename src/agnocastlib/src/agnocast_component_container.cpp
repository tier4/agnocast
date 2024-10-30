#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp_components/component_manager.hpp"

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  auto executor = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>();
  auto node = std::make_shared<rclcpp_components::ComponentManager>(executor);

  executor->add_node(node);
  executor->spin();

  rclcpp::shutdown();
  return 0;
}
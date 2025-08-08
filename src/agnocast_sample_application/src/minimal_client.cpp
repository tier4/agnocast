#include "agnocast_sample_interfaces/srv/sum_int_array.hpp"
#include "rclcpp/rclcpp.hpp"

using namespace std::chrono_literals;

constexpr size_t ARRAY_SIZE = 100;

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  auto node = rclcpp::Node::make_shared("minimal_client");
  auto client = node->create_client<agnocast_sample_interfaces::srv::SumIntArray>("sum_int_array");

  auto request = std::make_shared<agnocast_sample_interfaces::srv::SumIntArray::Request>();
  for (size_t i = 1; i <= ARRAY_SIZE; ++i) {
    request->data.push_back(i);
  }

  while (!client->wait_for_service(1s)) {
    if (!rclcpp::ok()) {
      RCLCPP_ERROR(node->get_logger(), "Interrupted while waiting for the service. Exiting.");
      return 0;
    }
    RCLCPP_INFO(node->get_logger(), "Service not available, waiting again...");
  }

  client->async_send_request(
    request,
    [node](rclcpp::Client<agnocast_sample_interfaces::srv::SumIntArray>::SharedFuture future) {
      RCLCPP_INFO(node->get_logger(), "Result: %ld", future.get()->sum);
    });

  rclcpp::spin(node);

  rclcpp::shutdown();
  return 0;
}

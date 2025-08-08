#include "agnocast_sample_interfaces/srv/sum_int_array.hpp"
#include "rclcpp/rclcpp.hpp"

class MinimalService : public rclcpp::Node
{
  rclcpp::Service<agnocast_sample_interfaces::srv::SumIntArray>::SharedPtr service_;

public:
  explicit MinimalService(const rclcpp::NodeOptions & options) : Node("minimal_service", options)
  {
    service_ = this->create_service<agnocast_sample_interfaces::srv::SumIntArray>(
      "sum_int_array",
      [this](
        const std::shared_ptr<agnocast_sample_interfaces::srv::SumIntArray::Request> request,
        std::shared_ptr<agnocast_sample_interfaces::srv::SumIntArray::Response> response) {
        response->sum = 0;
        for (int64_t value : request->data) {
          response->sum += value;
        }
        RCLCPP_INFO(this->get_logger(), "Sending back response: [%ld]", response->sum);
      });
  }
};

#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(MinimalService)

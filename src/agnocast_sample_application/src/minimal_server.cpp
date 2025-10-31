#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/srv/sum_int_array.hpp"
#include "rclcpp/rclcpp.hpp"

class MinimalService : public rclcpp::Node
{
  using RequestT = agnocast::Service<agnocast_sample_interfaces::srv::SumIntArray>::RequestT;
  using ResponseT = agnocast::Service<agnocast_sample_interfaces::srv::SumIntArray>::ResponseT;

  typename agnocast::Service<agnocast_sample_interfaces::srv::SumIntArray>::SharedPtr service_;

public:
  explicit MinimalService() : Node("minimal_server")
  {
    service_ = agnocast::create_service<agnocast_sample_interfaces::srv::SumIntArray>(
      this, "sum_int_array",
      [this](
        const agnocast::ipc_shared_ptr<RequestT> & request,
        agnocast::ipc_shared_ptr<ResponseT> & response) {
        response->sum = 0;
        for (int64_t value : request->data) {
          response->sum += value;
        }
        RCLCPP_INFO(this->get_logger(), "Sending back response: [%ld]", response->sum);
      });
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  agnocast::CallbackIsolatedAgnocastExecutor executor;
  auto node = std::make_shared<MinimalService>();
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

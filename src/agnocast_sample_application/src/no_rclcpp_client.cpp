#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/srv/sum_int_array.hpp"

#include <chrono>

using namespace std::chrono_literals;

constexpr size_t ARRAY_SIZE = 100;

class NoRclcppClient : public agnocast::Node
{
  using ServiceT = agnocast_sample_interfaces::srv::SumIntArray;
  using ClientT = agnocast::Client<ServiceT>;

  typename ClientT::SharedPtr client_;
  agnocast::TimerBase::SharedPtr timer_;
  bool request_sent_;

  void timer_callback()
  {
    if (!client_->service_is_ready()) {
      RCLCPP_INFO(this->get_logger(), "Service not available, waiting...");
      return;
    }

    if (request_sent_) {
      return;
    }
    request_sent_ = true;

    // Send first request with callback
    auto request1 = client_->borrow_loaned_request();
    for (size_t i = 1; i <= ARRAY_SIZE; ++i) {
      request1->data.push_back(i);
    }
    client_->async_send_request(std::move(request1), [this](ClientT::SharedFuture future) {
      RCLCPP_INFO(this->get_logger(), "Result1: %ld", future.get()->sum);
    });

    // Send second request and wait for result
    auto request2 = client_->borrow_loaned_request();
    for (size_t i = 0; i < ARRAY_SIZE; ++i) {
      request2->data.push_back(i);
    }
    auto future = client_->async_send_request(std::move(request2));
    RCLCPP_INFO(this->get_logger(), "Result2: %ld", future.get()->sum);
  }

public:
  explicit NoRclcppClient() : Node("no_rclcpp_client"), request_sent_(false)
  {
    client_ = this->create_client<ServiceT>("sum_int_array");
    timer_ = this->create_wall_timer(1s, std::bind(&NoRclcppClient::timer_callback, this));
  }
};

int main(int argc, char * argv[])
{
  agnocast::init(argc, argv);
  agnocast::AgnocastOnlySingleThreadedExecutor executor;
  auto node = std::make_shared<NoRclcppClient>();
  executor.add_node(node);
  executor.spin();
  agnocast::shutdown();
  return 0;
}

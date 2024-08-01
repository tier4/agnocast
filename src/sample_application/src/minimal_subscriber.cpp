#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "sample_interfaces/msg/static_size_array.hpp"

#include <chrono>
#include <fstream>
#include <vector>

uint64_t agnocast_get_timestamp()
{
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

using std::placeholders::_1;

class MinimalSubscriber : public rclcpp::Node
{
  std::vector<uint64_t> timestamps_;
  std::vector<uint64_t> timestamp_ids_;
  int timestamp_idx_ = 0;

  std::shared_ptr<agnocast::Subscription<sample_interfaces::msg::DynamicSizeArray>> sub_dynamic_;
  std::shared_ptr<agnocast::Subscription<sample_interfaces::msg::StaticSizeArray>> sub_static_;

  void callback_dynamic(
    const agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> & message)
  {
    timestamp_ids_[timestamp_idx_] = message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    RCLCPP_INFO(
      this->get_logger(), "I heard dynamic message: addr=%016lx",
      reinterpret_cast<uint64_t>(message.get()));
  }

  void callback_static(
    const agnocast::message_ptr<sample_interfaces::msg::StaticSizeArray> & message)
  {
    timestamp_ids_[timestamp_idx_] = message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    RCLCPP_INFO(
      this->get_logger(), "I heard static message: addr=%016lx",
      reinterpret_cast<uint64_t>(message.get()));
  }

public:
  MinimalSubscriber() : Node("minimal_subscriber")
  {
    sub_dynamic_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      "/my_dynamic_topic", 10, std::bind(&MinimalSubscriber::callback_dynamic, this, _1));
    sub_static_ = agnocast::create_subscription<sample_interfaces::msg::StaticSizeArray>(
      "/my_static_topic", rclcpp::QoS(10).transient_local(),
      std::bind(&MinimalSubscriber::callback_static, this, _1));

    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;
  }

  ~MinimalSubscriber()
  {
    {
      std::ofstream f("listener.log");

      if (!f) {
        std::cerr << "file open error" << std::endl;
        return;
      }

      for (int i = 0; i < timestamp_idx_; i++) {
        f << timestamp_ids_[i] << " " << timestamps_[i] << std::endl;
      }
    }
  }
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<MinimalSubscriber>());
  rclcpp::shutdown();
  return 0;
}

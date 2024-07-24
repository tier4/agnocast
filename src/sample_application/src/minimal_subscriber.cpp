#include <chrono>
#include <vector>
#include <fstream>

#include "rclcpp/rclcpp.hpp"

#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "agnocast.hpp"

uint64_t agnocast_get_timestamp() {
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

using std::placeholders::_1;

class MinimalSubscriber : public rclcpp::Node {
  std::vector<uint64_t> timestamps_;
  std::vector<uint64_t> timestamp_ids_;
  int timestamp_idx_ = 0;

  std::shared_ptr<agnocast::Subscription<sample_interfaces::msg::DynamicSizeArray>> sub_;

  void topic_callback(const agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> &message) {
    timestamp_ids_[timestamp_idx_] = message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();

    RCLCPP_INFO(this->get_logger(), "I heard message addr: %016lx", reinterpret_cast<uint64_t>(message.get()));

    /*
    for (size_t i = 0; i < message->data.size(); i++) {
      std::cout << message->data[i] << " ";
    }
    std::cout << std::endl;
    */
  }

public:

  MinimalSubscriber() : Node("minimal_subscriber") {
    sub_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      "/mytopic2", 10, std::bind(&MinimalSubscriber::topic_callback, this, _1));

    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;
  }

  ~MinimalSubscriber() {
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

int main(int argc, char * argv[]) {
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<MinimalSubscriber>());
  rclcpp::shutdown();
  return 0;
}

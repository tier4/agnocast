#include <chrono>
#include <vector>
#include <fstream>

#include "rclcpp/rclcpp.hpp"

#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "agnocast.hpp"

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

uint64_t agnocast_get_timestamp() {
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

class MinimalPublisher : public rclcpp::Node {
  void timer_callback() {
    agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> message = publisher_->borrow_loaned_message();

    message->id = count_;
    message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      message->data.push_back(i + count_);
    }
    count_++;

    RCLCPP_INFO(this->get_logger(), "publish message: %d", count_);

    timestamp_ids_[timestamp_idx_] = message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    publisher_->publish(std::move(message));
  }

  rclcpp::TimerBase::SharedPtr timer_;
  std::shared_ptr<agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>> publisher_;
  int count_;

  std::vector<uint64_t> timestamps_;
  std::vector<uint64_t> timestamp_ids_;
  int timestamp_idx_ = 0;

public:

  MinimalPublisher() : Node("minimal_publisher") {
    timer_ = this->create_wall_timer(100ms, std::bind(&MinimalPublisher::timer_callback, this));
    publisher_ = agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>("/mytopic");
    count_ = 0;

    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;
  }

  ~MinimalPublisher() {
    {
      std::ofstream f("talker.log");

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
  rclcpp::spin(std::make_shared<MinimalPublisher>());
  rclcpp::shutdown();
  return 0;
}

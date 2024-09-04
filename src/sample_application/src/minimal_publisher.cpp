#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "sample_interfaces/msg/static_size_array.hpp"

#include <chrono>
#include <fstream>
#include <vector>

using namespace std::chrono_literals;
const long long MESSAGE_SIZE = 1000ll * 1024;

uint64_t agnocast_get_timestamp()
{
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

class MinimalPublisher : public rclcpp::Node
{
  void assign_data(sample_interfaces::msg::StaticSizeArray & data)
  {
    for (int i = 0; i < 1000; i++) {
      data.data[i] = (i + count_) % 256;
    }
  }

  void timer_callback()
  {
    const auto timestamp = agnocast_get_timestamp();

    {
      agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> message =
        publisher_dynamic_->borrow_loaned_message();
      message->id = count_;
      message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
      for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
        message->data.push_back(i + count_);
      }

      // In order to test move constructor
      auto moved_message = std::move(message);

      publisher_dynamic_->publish(std::move(moved_message));
    }

    {
      agnocast::message_ptr<sample_interfaces::msg::StaticSizeArray> message =
        publisher_static_->borrow_loaned_message();
      message->id = count_;
      message->timestamp = timestamp;
      assign_data(*message);
      publisher_static_->publish(std::move(message));
    }

    timestamp_ids_[timestamp_idx_] = count_;
    timestamps_[timestamp_idx_] = timestamp;
    timestamp_idx_++;
    count_++;
    RCLCPP_INFO(this->get_logger(), "publish message: %d", count_);
  }

  rclcpp::TimerBase::SharedPtr timer_;
  std::shared_ptr<agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>> publisher_dynamic_;
  std::shared_ptr<agnocast::Publisher<sample_interfaces::msg::StaticSizeArray>> publisher_static_;
  int count_;

  std::vector<uint64_t> timestamps_;
  std::vector<uint64_t> timestamp_ids_;
  int timestamp_idx_ = 0;

public:
  MinimalPublisher() : Node("minimal_publisher")
  {
    timer_ = this->create_wall_timer(100ms, std::bind(&MinimalPublisher::timer_callback, this));
    publisher_dynamic_ =
      agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>("/my_dynamic_topic", 10);
    publisher_static_ =
      agnocast::create_publisher<sample_interfaces::msg::StaticSizeArray>("/my_static_topic", 10);
    count_ = 0;

    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;
  }

  ~MinimalPublisher()
  {
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

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<MinimalPublisher>());
  rclcpp::shutdown();
  return 0;
}

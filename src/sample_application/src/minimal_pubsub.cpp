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

using std::placeholders::_1;

class MinimalPubSub : public rclcpp::Node {

  void topic_callback(const agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> &sub_message) {
    // subscribe
    timestamp_ids_[timestamp_idx_] = sub_message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    RCLCPP_INFO(this->get_logger(), "I heard message addr: %016lx", reinterpret_cast<uint64_t>(sub_message.get()));

    // publish
    agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> pub_message = publisher_->borrow_loaned_message();
    pub_message->id = count_;
    pub_message->data.reserve(MESSAGE_SIZE / sizeof(uint64_t));
    for (size_t i = 0; i < MESSAGE_SIZE / sizeof(uint64_t); i++) {
      pub_message->data.push_back(i + count_);
    }
    count_++;
    RCLCPP_INFO(this->get_logger(), "publish message: %d", count_);
    timestamp_ids_[timestamp_idx_] = pub_message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    publisher_->publish(std::move(pub_message));
  }

  std::shared_ptr<agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>> publisher_;
  std::shared_ptr<agnocast::Subscription<sample_interfaces::msg::DynamicSizeArray>> sub_;
  int count_;

  std::vector<uint64_t> timestamps_;
  std::vector<uint64_t> timestamp_ids_;
  int timestamp_idx_ = 0;

public:

  MinimalPubSub() : Node("minimal_publisher") {
    publisher_ = agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>("/mytopic2");
    sub_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      "/mytopic", std::bind(&MinimalPubSub::topic_callback, this, _1));

    count_ = 0;

    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;
  }

  ~MinimalPubSub() {
    {
      std::ofstream f("listen_talker.log");

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
  agnocast::initialize_agnocast();
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<MinimalPubSub>());
  rclcpp::shutdown();
  return 0;
}

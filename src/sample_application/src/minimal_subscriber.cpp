#include "agnocast.hpp"
#include "rclcpp/rclcpp.hpp"
#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "sample_interfaces/msg/static_size_array.hpp"

#include <pthread.h>

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
  pthread_mutex_t timestamp_mtx = PTHREAD_MUTEX_INITIALIZER;

  agnocast::PollingSubscriber<sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr sub_static_;

  void callback_static(
    const agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> & message)
  {
    // Take dynamic message
    agnocast::ipc_shared_ptr<sample_interfaces::msg::DynamicSizeArray> dynamic_message =
      sub_dynamic_->takeData();

    pthread_mutex_lock(&timestamp_mtx);
    if (dynamic_message) {
      timestamp_ids_[timestamp_idx_] = dynamic_message->id;
      timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    }
    timestamp_ids_[timestamp_idx_] = message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    pthread_mutex_unlock(&timestamp_mtx);

    if (dynamic_message) {
      // In order to test copy constructor
      const auto copied_dynamic_message = dynamic_message;
      RCLCPP_INFO(
        this->get_logger(), "I took dynamic message: addr=%016lx",
        reinterpret_cast<uint64_t>(copied_dynamic_message.get()));
    }

    RCLCPP_INFO(
      this->get_logger(), "I heard static message: addr=%016lx",
      reinterpret_cast<uint64_t>(message.get()));
  }

public:
  MinimalSubscriber() : Node("minimal_subscriber")
  {
    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;

    rclcpp::CallbackGroup::SharedPtr group =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions options;
    options.callback_group = group;

    sub_dynamic_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      "/my_dynamic_topic", 10);

    sub_static_ = agnocast::create_subscription<sample_interfaces::msg::StaticSizeArray>(
      get_node_base_interface(), "/my_static_topic", rclcpp::QoS(10).transient_local(),
      std::bind(&MinimalSubscriber::callback_static, this, _1), options);
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

  agnocast::SingleThreadedAgnocastExecutor executor;
  executor.add_node(std::make_shared<MinimalSubscriber>());
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

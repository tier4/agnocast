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

  agnocast::PollingSubscriber<sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_dynamic_;
  agnocast::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr sub_static_;
  agnocast::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr sub_transient_local_;
  rclcpp::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr sub_transient_local_ros2_;
  agnocast::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr
    sub_transient_local_with_flag_;
  rclcpp::Subscription<sample_interfaces::msg::StaticSizeArray>::SharedPtr sub_transient_local_with_flag_ros2_;

  void callback_static(
    const agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> & message)
  {
    // Take dynamic message
    agnocast::ipc_shared_ptr<sample_interfaces::msg::DynamicSizeArray> dynamic_message =
      sub_dynamic_->takeData();

    if (dynamic_message) {
      timestamp_ids_[timestamp_idx_] = dynamic_message->id;
      timestamps_[timestamp_idx_++] = agnocast_get_timestamp();
    }
    timestamp_ids_[timestamp_idx_] = message->id;
    timestamps_[timestamp_idx_++] = agnocast_get_timestamp();

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

  void callback_transient_local(
    [[maybe_unused]] const agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> & message)
  {
    RCLCPP_INFO(
      this->get_logger(), "I heard transient_local message through Agnocast");
  }

  void callback_transient_local_ros2(
    [[maybe_unused]] const sample_interfaces::msg::StaticSizeArray & message)
  {
    RCLCPP_INFO(
      this->get_logger(), "I heard transient_local message through ROS");
  }

  void callback_transient_local_with_flag(
    [[maybe_unused]] const agnocast::ipc_shared_ptr<sample_interfaces::msg::StaticSizeArray> & message)
  {
    RCLCPP_INFO(
      this->get_logger(), "I heard transient_local_with_flag message through Agnocast");
  }

  void callback_transient_local_with_flag_ros2(
    [[maybe_unused]] const sample_interfaces::msg::StaticSizeArray & message)
  {
    RCLCPP_INFO(
      this->get_logger(), "I heard transient_local_with_flag message through ROS");
  }

public:
  explicit MinimalSubscriber(const rclcpp::NodeOptions & options)
  : Node("minimal_subscriber", options)
  {
    timestamps_.resize(10000, 0);
    timestamp_ids_.resize(10000, 0);
    timestamp_idx_ = 0;

    rclcpp::CallbackGroup::SharedPtr group =
      create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    agnocast::SubscriptionOptions agnocast_options;
    agnocast_options.callback_group = group;

    sub_dynamic_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
      "/my_dynamic_topic", 10);

    sub_static_ = agnocast::create_subscription<sample_interfaces::msg::StaticSizeArray>(
      get_node_base_interface(), "/my_static_topic", rclcpp::QoS(10).transient_local(),
      std::bind(&MinimalSubscriber::callback_static, this, _1), agnocast_options);

    sub_transient_local_ = agnocast::create_subscription<sample_interfaces::msg::StaticSizeArray>(
      get_node_base_interface(), "/my_transient_local_topic", rclcpp::QoS(1).transient_local(),
      std::bind(&MinimalSubscriber::callback_transient_local, this, _1));

    sub_transient_local_ros2_ = create_subscription<sample_interfaces::msg::StaticSizeArray>(
      "/my_transient_local_topic", rclcpp::QoS(1).transient_local(),
      std::bind(&MinimalSubscriber::callback_transient_local_ros2, this, _1));

    sub_transient_local_with_flag_ =
      agnocast::create_subscription<sample_interfaces::msg::StaticSizeArray>(
        get_node_base_interface(), "/my_transient_local_topic_with_flag",
        rclcpp::QoS(1).transient_local(),
        std::bind(&MinimalSubscriber::callback_transient_local_with_flag, this, _1));

    sub_transient_local_with_flag_ros2_ =
      create_subscription<sample_interfaces::msg::StaticSizeArray>(
        "/my_transient_local_topic_with_flag",
        rclcpp::QoS(1).transient_local(),
        std::bind(&MinimalSubscriber::callback_transient_local_with_flag_ros2, this, _1));
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

#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(MinimalSubscriber)

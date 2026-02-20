#include "agnocast/agnocast.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"

#include <chrono>

using namespace std::chrono_literals;

class NoRclcppTakeSubscriber : public agnocast::Node
{
  agnocast::PollingSubscriber<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr sub_;
  agnocast::TimerBase::SharedPtr timer_;

public:
  // Callback groups added for coverage testing
  rclcpp::CallbackGroup::SharedPtr manual_group_;
  rclcpp::CallbackGroup::SharedPtr late_auto_group_;

  explicit NoRclcppTakeSubscriber() : agnocast::Node("no_rclcpp_take_subscriber")
  {
    sub_ = this->create_subscription<agnocast_sample_interfaces::msg::DynamicSizeArray>(
      "/my_topic", rclcpp::QoS(rclcpp::KeepLast(1)));

    timer_ = this->create_wall_timer(1s, std::bind(&NoRclcppTakeSubscriber::timer_callback, this));

    // [Test Prep 1] Create a group with the auto-add flag set to false
    manual_group_ =
      this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive, false);

    RCLCPP_INFO(get_logger(), "NoRclcppTakeSubscriber started");
  }

  void create_late_group()
  {
    // [Test Prep 2] Create this after the node has been added to the Executor
    late_auto_group_ = this->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  }

private:
  void timer_callback()
  {
    auto message = sub_->take_data();
    if (message) {
      RCLCPP_INFO(
        get_logger(), "I heard dynamic size array message with id: %ld, size: %zu", message->id,
        message->data.size());
    }
  }
};

// [Added] Test Executor for calling protected methods
class TestExecutor : public agnocast::AgnocastOnlyMultiThreadedExecutor
{
public:
  void trigger_add_groups()
  {
    // Within a child class, we can call protected parent methods
    this->add_callback_groups_from_nodes_associated_to_executor();
  }
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);

  // Use the created test executor instead of the standard executor
  TestExecutor executor;
  auto node = std::make_shared<NoRclcppTakeSubscriber>();

  // Existing path 3: Automatic addition via add_node
  executor.add_node(node);

  // Uncovered path 1: Direct call to add_callback_group
  executor.add_callback_group(node->manual_group_, node->get_node_base_interface());

  // Uncovered path 2: Calling via the test executor
  node->create_late_group();
  executor.trigger_add_groups();

  executor.spin();
  return 0;
}

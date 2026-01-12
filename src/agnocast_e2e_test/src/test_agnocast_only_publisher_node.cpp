#include <agnocast/agnocast.hpp>

#include <std_msgs/msg/string.hpp>

#include <atomic>
#include <chrono>
#include <memory>
#include <thread>

class TestAgnocastOnlyPublisherNode : public agnocast::Node
{
public:
  explicit TestAgnocastOnlyPublisherNode(
    const rclcpp::NodeOptions & options = rclcpp::NodeOptions())
  : agnocast::Node("test_agnocast_only_publisher", options), count_(0)
  {
    publisher_ = this->create_publisher<std_msgs::msg::String>("test_topic", 10);

    // Start publishing thread
    publish_thread_ = std::thread([this]() {
      while (count_ < 10) {
        auto message = publisher_->borrow_loaned_message();
        message->data = "Hello from agnocast: " + std::to_string(count_++);
        RCLCPP_INFO(this->get_logger(), "Publishing: '%s'", message->data.c_str());
        publisher_->publish(std::move(message));
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
      }
    });

    if (publish_thread_.joinable()) {
      publish_thread_.join();
    }
  }

private:
  agnocast::Publisher<std_msgs::msg::String>::SharedPtr publisher_;
  std::atomic<int> count_;
  std::thread publish_thread_;
};

int main(int argc, char * argv[])
{
  rclcpp::init(argc, argv);

  auto node = std::make_shared<TestAgnocastOnlyPublisherNode>();
  auto executor = std::make_shared<agnocast::AgnocastOnlyCallbackIsolatedExecutor>();
  executor->add_node(node);

  executor->spin();

  rclcpp::shutdown();
  return 0;
}

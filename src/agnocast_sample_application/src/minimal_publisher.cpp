#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_node.hpp"
#include "agnocast_sample_interfaces/msg/dynamic_size_array.hpp"
#include "rclcpp/rclcpp.hpp"

using namespace std::chrono_literals;

class MinimalPublisher : public rclcpp::Node
{
  int64_t count_;
  rclcpp::TimerBase::SharedPtr timer_;
  agnocast::Publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>::SharedPtr
    publisher_dynamic_;
  agnocast::Node::SharedPtr agnocast_node_;

  // Parameters
  double publish_rate_;
  int64_t message_size_;
  std::string topic_name_;

  void timer_callback()
  {
    agnocast::ipc_shared_ptr<agnocast_sample_interfaces::msg::DynamicSizeArray> message =
      publisher_dynamic_->borrow_loaned_message();

    message->id = count_;
    message->data.reserve(message_size_ / sizeof(uint64_t));
    for (size_t i = 0; i < static_cast<size_t>(message_size_) / sizeof(uint64_t); i++) {
      message->data.push_back(i + count_);
    }

    publisher_dynamic_->publish(std::move(message));
    RCLCPP_INFO(this->get_logger(), "publish message: id=%ld", count_++);
  }

public:
  MinimalPublisher() : Node("minimal_publisher")
  {
    count_ = 0;

    // Create agnocast::Node for parameter and topic name resolution
    // GlobalContext has already been initialized by agnocast::init()
    agnocast_node_ = std::make_shared<agnocast::Node>("minimal_publisher");

    // Declare parameters with default values
    agnocast_node_->declare_parameter("publish_rate", 10.0);
    agnocast_node_->declare_parameter("message_size", static_cast<int64_t>(1000 * 1024));
    agnocast_node_->declare_parameter("topic_name", std::string("my_topic"));

    // Get parameter values
    agnocast_node_->get_parameter("publish_rate", publish_rate_);
    agnocast_node_->get_parameter("message_size", message_size_);
    agnocast_node_->get_parameter("topic_name", topic_name_);

    // Resolve topic name (handles remapping, namespace, etc.)
    std::string resolved_topic = agnocast_node_->resolve_topic_name(topic_name_);

    // Log parameter values for verification
    RCLCPP_INFO(this->get_logger(), "=== Agnocast Node Parameters ===");
    RCLCPP_INFO(this->get_logger(), "Node name: %s", agnocast_node_->get_name().c_str());
    RCLCPP_INFO(this->get_logger(), "Namespace: %s", agnocast_node_->get_namespace().c_str());
    RCLCPP_INFO(this->get_logger(), "Fully qualified name: %s", agnocast_node_->get_fully_qualified_name().c_str());
    RCLCPP_INFO(this->get_logger(), "Publish rate: %.2f Hz", publish_rate_);
    RCLCPP_INFO(this->get_logger(), "Message size: %ld bytes", message_size_);
    RCLCPP_INFO(this->get_logger(), "Topic name (input): %s", topic_name_.c_str());
    RCLCPP_INFO(this->get_logger(), "Topic name (resolved): %s", resolved_topic.c_str());
    RCLCPP_INFO(this->get_logger(), "================================");

    // Create publisher with resolved topic name
    publisher_dynamic_ =
      agnocast::create_publisher<agnocast_sample_interfaces::msg::DynamicSizeArray>(
        this, resolved_topic, 1);

    // Create timer with parameterized rate
    auto timer_period = std::chrono::duration<double>(1.0 / publish_rate_);
    timer_ = this->create_wall_timer(
      std::chrono::duration_cast<std::chrono::nanoseconds>(timer_period),
      std::bind(&MinimalPublisher::timer_callback, this));
  }
};

int main(int argc, char * argv[])
{
  // Initialize global context with command-line arguments
  // Corresponds to rclcpp::init()
  agnocast::init(argc, argv);
  rclcpp::init(argc, argv);

  agnocast::SingleThreadedAgnocastExecutor executor;
  auto node = std::make_shared<MinimalPublisher>();
  executor.add_node(node);
  executor.spin();

  rclcpp::shutdown();
  return 0;
}

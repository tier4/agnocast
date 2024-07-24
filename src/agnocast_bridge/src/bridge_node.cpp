#include <queue>

#include "rclcpp/rclcpp.hpp"

#include "sample_interfaces/msg/dynamic_size_array.hpp"
#include "agnocast.hpp"

using namespace std::chrono_literals;
using std::placeholders::_1;

class BridgeNode : public rclcpp::Node
{
    std::shared_ptr<agnocast::Publisher<sample_interfaces::msg::DynamicSizeArray>> agnocast_publisher_;
    std::shared_ptr<agnocast::Subscription<sample_interfaces::msg::DynamicSizeArray>> agnocast_subscriber_;

    rclcpp::Subscription<sample_interfaces::msg::DynamicSizeArray>::SharedPtr subscription_;
    rclcpp::Publisher<sample_interfaces::msg::DynamicSizeArray>::SharedPtr publisher_;

    // Assume single thread
    std::queue<unsigned long long> que;

    void topic_callback(sample_interfaces::msg::DynamicSizeArray::UniquePtr msg) {
        /*
        if (!que.empty() && que.front() == reinterpret_cast<unsigned long long>(msg.get())) {
            RCLCPP_INFO(this->get_logger(), "skip subscription callback");
            que.pop();
            return;
        }
        */
        if (!que.empty() && msg->id == que.front()) {
            RCLCPP_INFO(this->get_logger(), "skip subscription callback");
            que.pop();
            return;
        }

        RCLCPP_INFO(this->get_logger(), "bridge message ros2->agnocast address: %p", msg.get());

        auto raw = msg.release();
        agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> message = agnocast_publisher_->borrow_loaned_message(raw);
        agnocast_publisher_->publish(std::move(message));
    }

    void agnocast_topic_callback(const agnocast::message_ptr<sample_interfaces::msg::DynamicSizeArray> &message) {
        //RCLCPP_INFO(this->get_logger(), "I heard message addr: %016lx", reinterpret_cast<uint64_t>(message.get()));

        if (message.get_publisher_pid() == getpid()) {
            RCLCPP_INFO(this->get_logger(), "skip subscription callback");
            return;
        }

        RCLCPP_INFO(this->get_logger(), "bridge message agnocast->ros2 address: %p", message.get());

        que.push(message->id);
        const sample_interfaces::msg::DynamicSizeArray *raw = message.get();
        publisher_->publish(*raw);
    }

public:
    BridgeNode() : Node("my_node")
    {
        auto publisher_options = rclcpp::PublisherOptions();
        publisher_options.use_intra_process_comm = rclcpp::IntraProcessSetting::Enable;
        publisher_ = this->create_publisher<sample_interfaces::msg::DynamicSizeArray>("mytopic", 10, publisher_options);

        auto subscription_options = rclcpp::SubscriptionOptions();
        subscription_options.use_intra_process_comm = rclcpp::IntraProcessSetting::Enable;
        subscription_ = this->create_subscription<sample_interfaces::msg::DynamicSizeArray>(
            "mytopic", 10, std::bind(&BridgeNode::topic_callback, this, _1), subscription_options);

        agnocast_publisher_ = agnocast::create_publisher<sample_interfaces::msg::DynamicSizeArray>("/mytopic", 10);

        agnocast_subscriber_ = agnocast::create_subscription<sample_interfaces::msg::DynamicSizeArray>(
            "/mytopic", 10, std::bind(&BridgeNode::agnocast_topic_callback, this, _1));
    }
};

int main(int argc, char * argv[])
{
    rclcpp::init(argc, argv);

    auto node = std::make_shared<BridgeNode>();
    rclcpp::spin(node);

    rclcpp::shutdown();
    return 0;
}

#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "rclcpp/rclcpp.hpp"

#include <regex>

namespace agnocast
{

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const BridgeArgs &);

void bridge_process_main(const MqMsgBridge & msg);
QoSFlat flatten_qos(const rclcpp::QoS & qos);
rclcpp::QoS reconstruct_qos(const QoSFlat & q);

template <typename MessageT>
class BridgeNode : public rclcpp::Node
{
public:
  explicit BridgeNode(const BridgeArgs & args)
  : rclcpp::Node(
      "agnocast_bridge" + std::regex_replace(std::string(args.topic_name), std::regex("/"), "_"))
  {
    std::string topic_name(args.topic_name);
    rclcpp::QoS qos = reconstruct_qos(args.qos);

    agnocast::PublisherOptions pub_options;
    pub_options.send_a2r_bridge_request = false;
    agnocast_pub_ =
      std::make_shared<agnocast::Publisher<MessageT>>(this, topic_name, qos, pub_options);

    auto callback = [this](const typename MessageT::ConstSharedPtr msg) {
      auto loaned_msg = this->agnocast_pub_->borrow_loaned_message();
      *loaned_msg = *msg;
      this->agnocast_pub_->publish(std::move(loaned_msg));
    };

    rclcpp::SubscriptionOptions sub_options;
    sub_options.ignore_local_publications = true;
    ros_sub_ = this->create_subscription<MessageT>(topic_name, qos, callback, sub_options);
  }

private:
  typename agnocast::Publisher<MessageT>::SharedPtr agnocast_pub_;
  typename rclcpp::Subscription<MessageT>::SharedPtr ros_sub_;
};

template <typename MessageT>
std::shared_ptr<rclcpp::Node> start_bridge_node(const BridgeArgs & args)
{
  return std::make_shared<BridgeNode<MessageT>>(args);
}

}  // namespace agnocast

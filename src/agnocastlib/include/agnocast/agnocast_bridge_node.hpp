#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <regex>

namespace agnocast
{

template <typename MessageT>
class BridgeNode : public rclcpp::Node
{
public:
  explicit BridgeNode(const BridgeArgs & args)
  : rclcpp::Node(
      "agnocast_bridge" + std::regex_replace(std::string(args.topic_name), std::regex("/"), "_"))
  {
    std::string topic_name(args.topic_name);

    rclcpp::QoS qos(args.qos.depth);
    if (args.qos.history == 1) {
      qos.keep_all();
    }
    if (args.qos.reliability == 1) {
      qos.reliable();
    } else if (args.qos.reliability == 2) {
      qos.best_effort();
    }
    if (args.qos.durability == 1) {
      qos.transient_local();
    }

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

    ros_pub_ = this->create_publisher<MessageT>(topic_name, qos);

    auto agnocast_callback = [this](const typename MessageT::ConstSharedPtr msg) {
      auto loaned_msg = this->ros_pub_->borrow_loaned_message();
      *loaned_msg = *msg;
      this->ros_pub_->publish(std::move(loaned_msg));
    };

    agnocast::SubscriptionOptions agnocast_sub_options;
    agnocast_sub_options.send_r2a_bridge_request = false;
    agnocast_sub_ = std::make_shared<agnocast::Subscription<MessageT>>(
      this, topic_name, qos, agnocast_callback, agnocast_sub_options);
  }

private:
  typename agnocast::Publisher<MessageT>::SharedPtr agnocast_pub_;
  typename rclcpp::Subscription<MessageT>::SharedPtr ros_sub_;

  typename rclcpp::Publisher<MessageT>::SharedPtr ros_pub_;
  typename agnocast::Subscription<MessageT>::SharedPtr agnocast_sub_;
};

template <typename MessageT>
std::shared_ptr<rclcpp::Node> start_bridge_node(const BridgeArgs & args)
{
  return std::make_shared<BridgeNode<MessageT>>(args);
}

}  // namespace agnocast

#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "rclcpp/rclcpp.hpp"

#include <functional>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace agnocast
{
using BridgeSetupFunction = std::function<rclcpp::SubscriptionBase::SharedPtr(
  rclcpp::Node::SharedPtr, const std::string &, const rclcpp::QoS &)>;

std::map<std::string, BridgeSetupFunction> & get_bridge_factory_map();

template <typename MessageT>
class BridgeRegistrar
{
public:
  explicit BridgeRegistrar(const std::string & type_name)
  {
    get_bridge_factory_map()[type_name] =
      [](
        rclcpp::Node::SharedPtr node, const std::string & topic_name,
        const rclcpp::QoS & qos) -> rclcpp::SubscriptionBase::SharedPtr {
      auto logger = node->get_logger();

      agnocast::PublisherOptions pub_options;
      auto internal_agno_publisher =
        std::make_shared<agnocast::Publisher<MessageT>>(node.get(), topic_name, qos, pub_options);

      auto ros2_callback = [logger,
                            internal_agno_publisher](const typename MessageT::ConstSharedPtr msg) {
        auto loaned_msg = internal_agno_publisher->borrow_loaned_message();
        *loaned_msg = *msg;
        internal_agno_publisher->publish(std::move(loaned_msg));
      };

      rclcpp::SubscriptionOptions sub_options;
      sub_options.callback_group =
        node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
      sub_options.ignore_local_publications = true;

      auto sub = node->create_subscription<MessageT>(topic_name, qos, ros2_callback, sub_options);
      return sub;
    };
  }
};

}  // namespace agnocast
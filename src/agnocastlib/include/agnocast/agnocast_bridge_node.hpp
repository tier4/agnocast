#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast

{

template <typename MessageT>
void send_bridge_request(const std::string & topic_name, topic_local_id_t id, BridgeDirection dir)
{
  (void)topic_name;  // TODO: Remove
  (void)id;          // TODO: Remove
  (void)dir;         // TODO: Remove
  // TODO: Implement the actual message queue communication to request a bridge.
  // Note: This implementation depends on AgnocastPublisher and AgnocastSubscription.
}

// Policy for agnocast::Subscription.
// Requests a bridge that forwards messages from ROS 2 to Agnocast (R2A).
struct RosToAgnocastRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, topic_local_id_t id)
  {
    send_bridge_request<MessageT>(topic_name, id, BridgeDirection::ROS2_TO_AGNOCAST);
  }
};

// Policy for agnocast::Publisher.
// Requests a bridge that forwards messages from Agnocast to ROS 2 (A2R).
struct AgnocastToRosRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, topic_local_id_t id)
  {
    send_bridge_request<MessageT>(topic_name, id, BridgeDirection::AGNOCAST_TO_ROS2);
  }
};

// Dummy policy to avoid circular header dependencies.
// Used internally by BridgeNode, Service, and Client where bridge requests
// are not needed and would cause include cycles.
struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, const rclcpp::QoS &)
  {
    // Do nothing
  }
};

template <typename MessageT>
class RosToAgnocastBridge
{
  using AgnoPub = agnocast::BasicPublisher<MessageT, NoBridgeRequestPolicy>;
  typename AgnoPub::SharedPtr agnocast_pub_;
  typename rclcpp::Subscription<MessageT>::SharedPtr ros_sub_;
  rclcpp::CallbackGroup::SharedPtr ros_cb_group_;

public:
  explicit RosToAgnocastBridge(
    rclcpp::Node::SharedPtr parent_node, const std::string & topic_name,
    const rclcpp::QoS & sub_qos)
  {
    // Agnocast relies on shared memory, so network reliability concepts do not apply.
    // TransientLocal is hardcoded here as a catch-all configuration that supports
    // any subscriber requirement (volatile or durable) by preserving data.
    agnocast_pub_ = std::make_shared<AgnoPub>(
      parent_node.get(), topic_name, rclcpp::QoS(10).transient_local(),
      agnocast::PublisherOptions{});
    ros_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    rclcpp::SubscriptionOptions ros_opts;
    ros_opts.ignore_local_publications = true;
    ros_opts.callback_group = ros_cb_group_;
    auto pub_ptr = agnocast_pub_;

    // The ROS subscription acts as a proxy for the requesting Agnocast subscriber.
    // sub_qos applies the Agnocast subscriber's settings (e.g. history depth)
    // to the ROS side to ensure the bridge satisfies the downstream requirements.
    ros_sub_ = parent_node->create_subscription<MessageT>(
      topic_name, sub_qos,
      [pub_ptr](const typename MessageT::ConstSharedPtr msg) {
        auto loaned_msg = pub_ptr->borrow_loaned_message();
        *loaned_msg = *msg;
        pub_ptr->publish(std::move(loaned_msg));
      },
      ros_opts);
  }
};

}  // namespace agnocast

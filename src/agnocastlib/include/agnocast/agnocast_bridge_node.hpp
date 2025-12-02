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

}  // namespace agnocast

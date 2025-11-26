#pragma once

#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast

{

template <typename MessageT>
void send_bridge_request(const std::string & topic_name, const rclcpp::QoS & qos)
{
  (void)topic_name;  // TODO: Remove
  (void)qos;         // TODO: Remove
  // TODO: Implement the actual message queue communication to request a bridge.
  // Note: This implementation depends on AgnocastPublisher and AgnocastSubscription.
}

// Default policy for user-facing Publisher/Subscription.
// Requests a bridge to be created for the topic.
struct DefaultBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    send_bridge_request<MessageT>(topic_name, qos);
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

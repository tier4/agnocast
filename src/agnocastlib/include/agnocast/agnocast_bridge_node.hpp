#pragma once

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast

{

static constexpr size_t DEFAULT_QOS_DEPTH = 10;

template <typename MessageT>
void send_bridge_request(
  const std::string & topic_name, topic_local_id_t id, BridgeDirection direction);

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
  static void request_bridge(const std::string & /*unused*/, const rclcpp::QoS & /*unused*/)
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
    const rclcpp::Node::SharedPtr & parent_node, const std::string & topic_name,
    const rclcpp::QoS & sub_qos)
  {
    // Agnocast relies on shared memory, so network reliability concepts do not apply.
    // TransientLocal is hardcoded here as a catch-all configuration that supports
    // any subscriber requirement (volatile or durable) by preserving data.
    agnocast_pub_ = std::make_shared<AgnoPub>(
      parent_node.get(), topic_name, rclcpp::QoS(DEFAULT_QOS_DEPTH).transient_local(),
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
      [this](const typename MessageT::ConstSharedPtr msg) {
        auto loaned_msg = this->agnocast_pub_->borrow_loaned_message();
        *loaned_msg = *msg;
        this->agnocast_pub_->publish(std::move(loaned_msg));
      },
      ros_opts);
  }
};

// We should document that things don't work well when Agnocast publishers have a mix of transient
// local and volatile durability settings. If we ever face a requirement to support topics with
// such mixed durability settings, we could achieve this by creating Agnocast subscribers with
// transient local, and making an exception so that only Agnocast subscribers used for the bridge
// feature can also receive from volatile Agnocast publishers. (This isn't very clean, so we'd
// prefer to avoid it if possible.)
template <typename MessageT>
class AgnocastToRosBridge
{
  using AgnoSub = agnocast::BasicSubscription<MessageT, NoBridgeRequestPolicy>;
  typename rclcpp::Publisher<MessageT>::SharedPtr ros_pub_;
  typename AgnoSub::SharedPtr agnocast_sub_;
  rclcpp::CallbackGroup::SharedPtr agno_cb_group_;

public:
  explicit AgnocastToRosBridge(
    const rclcpp::Node::SharedPtr & parent_node, const std::string & topic_name,
    const rclcpp::QoS & sub_qos)
  {
    // ROS Publisher configuration acts as a source for downstream ROS nodes.
    // We use Reliable and TransientLocal as a "catch-all" configuration.
    // This ensures that this bridge can serve both Volatile and Durable (TransientLocal)
    // ROS subscribers without connectivity issues.
    ros_pub_ = parent_node->create_publisher<MessageT>(
      topic_name, rclcpp::QoS(DEFAULT_QOS_DEPTH).reliable().transient_local());
    agno_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions agno_opts;
    agno_opts.ignore_local_publications = true;
    agno_opts.callback_group = agno_cb_group_;

    // Subscribe to Agnocast (shared memory).
    // The QoS settings are now passed via argument to inherit the settings
    // from the corresponding Agnocast publisher (e.g. Reliable or BestEffort).
    agnocast_sub_ = std::make_shared<AgnoSub>(
      parent_node.get(), topic_name, sub_qos,
      [this](const agnocast::ipc_shared_ptr<MessageT> msg) {
        auto loaned_msg = this->ros_pub_->borrow_loaned_message();
        if (loaned_msg.is_valid()) {
          loaned_msg.get() = *msg;
          this->ros_pub_->publish(std::move(loaned_msg));
        } else {
          this->ros_pub_->publish(*msg);
        }
      },
      agno_opts);
  }
};

template <typename MessageT>
std::shared_ptr<void> start_ros_to_agno_node(
  rclcpp::Node::SharedPtr node, const BridgeTargetInfo & info)
{
  // TODO(yutarokobayashi): Implementation of get_subscriber_qos
  return std::make_shared<RosToAgnocastBridge<MessageT>>(node, info.topic_name, rclcpp::QoS(10));
}

template <typename MessageT>
std::shared_ptr<void> start_agno_to_ros_node(
  rclcpp::Node::SharedPtr node, const BridgeTargetInfo & info)
{
  // TODO(yutarokobayashi): Implementation of get_publisher_qos
  return std::make_shared<AgnocastToRosBridge<MessageT>>(node, info.topic_name, rclcpp::QoS(10));
}

template <typename MessageT>
void send_bridge_request(
  const std::string & topic_name, topic_local_id_t id, BridgeDirection direction)
{
  (void)topic_name;  // TODO(yutarokobayashi): Remove
  (void)id;          // TODO(yutarokobayashi): Remove

  // We capture 'fn_reverse' because bridge_manager is responsible for managing both directions
  // independently. Storing the reverse factory allows us to instantiate the return path on-demand
  // within the same process.
  auto fn_current = (direction == BridgeDirection::ROS2_TO_AGNOCAST)
                      ? &start_ros_to_agno_node<MessageT>
                      : &start_agno_to_ros_node<MessageT>;
  auto fn_reverse = (direction == BridgeDirection::ROS2_TO_AGNOCAST)
                      ? &start_agno_to_ros_node<MessageT>
                      : &start_ros_to_agno_node<MessageT>;

  (void)fn_current;  // TODO(yutarokobayashi): Remove
  (void)fn_reverse;  // TODO(yutarokobayashi): Remove

  // TODO(yutarokobayashi): Implement the actual message queue communication to request a bridge.
  // std::string mq_name = create_mq_name_for_bridge_parent(getppid());
}

}  // namespace agnocast

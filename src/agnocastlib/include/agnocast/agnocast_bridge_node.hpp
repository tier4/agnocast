#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <mqueue.h>
#include <unistd.h>

#include <cstring>
#include <memory>
#include <string>
#include <vector>

namespace agnocast
{

template <typename MessageT>
void send_bridge_command(const std::string & topic_name, topic_local_id_t id, BridgeDirection dir);

// =========================================================================
// Request Policies
// =========================================================================

struct RosToAgnocastRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, topic_local_id_t id)
  {
    send_bridge_command<MessageT>(topic_name, id, BridgeDirection::ROS2_TO_AGNOCAST);
  }
};

struct AgnocastToRosRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, topic_local_id_t id)
  {
    send_bridge_command<MessageT>(topic_name, id, BridgeDirection::AGNOCAST_TO_ROS2);
  }
};

struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, topic_local_id_t)
  {
  }
};

// =========================================================================
// Class 1: ROS -> Agnocast Bridge (Receiver)
// =========================================================================
template <typename MessageT>
class RosToAgnocastBridge
{
private:
  using AgnoPub = agnocast::BasicPublisher<MessageT, NoBridgeRequestPolicy>;
  using RosSubPtr = typename rclcpp::Subscription<MessageT>::SharedPtr;

  typename AgnoPub::SharedPtr agnocast_pub_;
  RosSubPtr ros_sub_;
  rclcpp::CallbackGroup::SharedPtr ros_cb_group_;

public:
  explicit RosToAgnocastBridge(
    rclcpp::Node::SharedPtr parent_node, const std::string & topic_name,
    const rclcpp::QoS & sub_qos)
  {
    agnocast_pub_ = std::make_shared<AgnoPub>(
      parent_node.get(), topic_name, rclcpp::QoS(10).reliable().transient_local(),
      agnocast::PublisherOptions{});

    ros_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    rclcpp::SubscriptionOptions ros_opts;
    ros_opts.ignore_local_publications = true;
    ros_opts.callback_group = ros_cb_group_;

    auto pub_ptr = agnocast_pub_;

    ros_sub_ = parent_node->create_subscription<MessageT>(
      topic_name, sub_qos,
      [pub_ptr](const typename MessageT::ConstSharedPtr msg) {
        auto loaned_msg = pub_ptr->borrow_loaned_message();
        *loaned_msg = *msg;
        pub_ptr->publish(std::move(loaned_msg));
      },
      ros_opts);
    RCLCPP_INFO(parent_node->get_logger(), "Started R2A bridge for '%s'", topic_name.c_str());
  }
};

// =========================================================================
// Class 2: Agnocast -> ROS Bridge (Sender)
// =========================================================================
template <typename MessageT>
class AgnocastToRosBridge
{
private:
  using AgnoSub = agnocast::BasicSubscription<MessageT, NoBridgeRequestPolicy>;
  using RosPubPtr = typename rclcpp::Publisher<MessageT>::SharedPtr;

  RosPubPtr ros_pub_;
  typename AgnoSub::SharedPtr agnocast_sub_;
  rclcpp::CallbackGroup::SharedPtr agno_cb_group_;

public:
  explicit AgnocastToRosBridge(rclcpp::Node::SharedPtr parent_node, const std::string & topic_name)
  {
    auto bridge_qos = rclcpp::QoS(1).reliable().durability_volatile();
    ros_pub_ = parent_node->create_publisher<MessageT>(topic_name, bridge_qos);

    agno_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions agno_opts;
    agno_opts.ignore_local_publications = true;
    agno_opts.callback_group = agno_cb_group_;

    auto pub_ptr = ros_pub_;

    agnocast_sub_ = std::make_shared<AgnoSub>(
      parent_node.get(), topic_name, rclcpp::QoS(10).best_effort().durability_volatile(),
      [pub_ptr](const agnocast::ipc_shared_ptr<MessageT> msg) {
        if (pub_ptr->get_subscription_count() == 0) {
          return;
        }
        auto loaned_msg = pub_ptr->borrow_loaned_message();
        loaned_msg.get() = *msg;
        pub_ptr->publish(std::move(loaned_msg));
      },
      agno_opts);

    RCLCPP_INFO(parent_node->get_logger(), "Started A2R bridge for '%s'", topic_name.c_str());
  }
};

// =========================================================================
// Helper: Fetch QoS from Kernel (Generator Context)
// =========================================================================

inline rclcpp::QoS get_subscriber_qos(const char * topic_name, topic_local_id_t id)
{
  struct ioctl_get_subscriber_qos_args args = {};
  snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", topic_name);
  args.id = id;

  if (ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_QOS_CMD, &args) < 0) {
    RCLCPP_WARN(
      rclcpp::get_logger("agnocast_bridge"), "Failed to fetch QoS for '%s' (ID:%d). Using default.",
      topic_name, id);
    return rclcpp::QoS(10);
  }

  rclcpp::QoS qos(args.qos.depth);
  if (args.qos.is_transient_local) {
    qos.transient_local();
  } else {
    qos.durability_volatile();
  }

  if (args.qos.is_reliable) {
    qos.reliable();
  } else {
    qos.best_effort();
  }

  return qos;
}

// =========================================================================
// Factory Functions
// =========================================================================
template <typename MessageT>
std::shared_ptr<void> start_ros_to_agno_node(
  rclcpp::Node::SharedPtr node, const BridgeTargetInfo & info)
{
  rclcpp::QoS qos = get_subscriber_qos(info.topic_name, info.target_id);
  return std::make_shared<RosToAgnocastBridge<MessageT>>(node, info.topic_name, qos);
}

template <typename MessageT>
std::shared_ptr<void> start_agno_to_ros_node(
  rclcpp::Node::SharedPtr node, const BridgeTargetInfo & info)
{
  return std::make_shared<AgnocastToRosBridge<MessageT>>(node, info.topic_name);
}

// =========================================================================
// Helper: Send Command (MQ)
// =========================================================================

template <typename MessageT>
void send_bridge_command(const std::string & topic_name, topic_local_id_t id, BridgeDirection dir)
{
  static auto logger = rclcpp::get_logger("agnocast_bridge_requester");

  MqMsgBridge msg = {};

  msg.direction = dir;
  snprintf(msg.target.topic_name, MAX_NAME_LENGTH, "%s", topic_name.c_str());
  msg.target.target_id = id;

  BridgeFn fn_current = (dir == BridgeDirection::ROS2_TO_AGNOCAST)
                          ? &start_ros_to_agno_node<MessageT>
                          : &start_agno_to_ros_node<MessageT>;

  BridgeFn fn_reverse = (dir == BridgeDirection::ROS2_TO_AGNOCAST)
                          ? &start_agno_to_ros_node<MessageT>
                          : &start_ros_to_agno_node<MessageT>;

  Dl_info info = {};
  if (dladdr(reinterpret_cast<void *>(fn_current), &info) == 0) {
    RCLCPP_ERROR(logger, "dladdr failed: cannot locate bridge factory function.");
    return;
  }

  const uintptr_t base_addr = reinterpret_cast<uintptr_t>(info.dli_fbase);

  if (info.dli_fname) {
    snprintf(msg.factory.shared_lib_path, MAX_NAME_LENGTH, "%s", info.dli_fname);
  } else {
    RCLCPP_ERROR(logger, "dladdr returned NULL filename.");
    return;
  }

  const char * symbol_name = info.dli_sname ? info.dli_sname : "__MAIN_EXECUTABLE__";
  snprintf(msg.factory.symbol_name, MAX_NAME_LENGTH, "%s", symbol_name);

  msg.factory.fn_offset = reinterpret_cast<uintptr_t>(fn_current) - base_addr;
  msg.factory.fn_offset_reverse = reinterpret_cast<uintptr_t>(fn_reverse) - base_addr;

  const std::string mq_name_str = create_mq_name_for_bridge_parent(getpid());
  mqd_t mq = mq_open(mq_name_str.c_str(), O_WRONLY);

  if (mq == (mqd_t)-1) {
    return;
  }

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) < 0) {
    RCLCPP_ERROR(logger, "mq_send failed: %s", strerror(errno));
  }
  mq_close(mq);
}

}  // namespace agnocast
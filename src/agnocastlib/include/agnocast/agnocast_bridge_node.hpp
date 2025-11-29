#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"
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

// 外部定義関数
extern "C" {
std::string create_mq_name_for_bridge_parent(const pid_t pid);
}

namespace agnocast
{

// 前方宣言
template <typename MessageT>
void send_bridge_command(
  const std::string & topic_name, const rclcpp::QoS & qos, BridgeDirection dir, BridgeCommand cmd);

// =========================================================================
// Request Policies
// =========================================================================

struct RosToAgnocastRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    send_bridge_command<MessageT>(
      topic_name, qos, BridgeDirection::ROS2_TO_AGNOCAST, BridgeCommand::CREATE_BRIDGE);
  }

  template <typename MessageT>
  static void release_bridge(const std::string & topic_name)
  {
    send_bridge_command<MessageT>(
      topic_name, rclcpp::QoS(1), BridgeDirection::ROS2_TO_AGNOCAST, BridgeCommand::REMOVE_BRIDGE);
  }
};

struct AgnocastToRosRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    send_bridge_command<MessageT>(
      topic_name, qos, BridgeDirection::AGNOCAST_TO_ROS2, BridgeCommand::CREATE_BRIDGE);
  }

  template <typename MessageT>
  static void release_bridge(const std::string & topic_name)
  {
    send_bridge_command<MessageT>(
      topic_name, rclcpp::QoS(1), BridgeDirection::AGNOCAST_TO_ROS2, BridgeCommand::REMOVE_BRIDGE);
  }
};

struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, const rclcpp::QoS &)
  {
  }
  template <typename MessageT>
  static void release_bridge(const std::string &)
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

    // Use-after-free 防止:
    // コールバック実行中に this が破棄されても、pub_ptr が生きている限り
    // パブリッシャーの実体は生存し続ける。
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
  explicit AgnocastToRosBridge(
    rclcpp::Node::SharedPtr parent_node, const std::string & topic_name,
    [[maybe_unused]] const rclcpp::QoS & pub_qos)
  {
    auto bridge_qos = rclcpp::QoS(1).reliable().durability_volatile();
    ros_pub_ = parent_node->create_publisher<MessageT>(topic_name, bridge_qos);

    agno_cb_group_ =
      parent_node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

    agnocast::SubscriptionOptions agno_opts;
    agno_opts.ignore_local_publications = true;
    agno_opts.callback_group = agno_cb_group_;

    // Use-after-free 防止
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
// Factory Functions
// =========================================================================

template <typename MessageT>
std::shared_ptr<void> start_ros_to_agno_node(rclcpp::Node::SharedPtr node, const BridgeArgs & args)
{
  auto qos = reconstruct_qos_from_flat(args.qos);
  return std::make_shared<RosToAgnocastBridge<MessageT>>(node, args.topic_name, qos);
}

template <typename MessageT>
std::shared_ptr<void> start_agno_to_ros_node(rclcpp::Node::SharedPtr node, const BridgeArgs & args)
{
  auto qos = reconstruct_qos_from_flat(args.qos);
  return std::make_shared<AgnocastToRosBridge<MessageT>>(node, args.topic_name, qos);
}

// =========================================================================
// Helper: Send Command (MQ)
// =========================================================================

template <typename MessageT>
void send_bridge_command(
  const std::string & topic_name, const rclcpp::QoS & qos, BridgeDirection dir, BridgeCommand cmd)
{
  auto logger = rclcpp::get_logger("agnocast_bridge_requester");
  MqMsgBridge msg = {};
  msg.direction = dir;
  msg.command = cmd;

  BridgeFn fn_current = nullptr;
  BridgeFn fn_reverse = nullptr;

  if (dir == BridgeDirection::ROS2_TO_AGNOCAST) {
    fn_current = &start_ros_to_agno_node<MessageT>;
    fn_reverse = &start_agno_to_ros_node<MessageT>;
  } else {
    fn_current = &start_agno_to_ros_node<MessageT>;
    fn_reverse = &start_ros_to_agno_node<MessageT>;
  }

  Dl_info info{};
  if (dladdr(reinterpret_cast<void *>(fn_current), &info) == 0) {
    RCLCPP_ERROR(logger, "dladdr failed: cannot locate bridge factory function.");
    return;
  }

  uintptr_t base_addr = reinterpret_cast<uintptr_t>(info.dli_fbase);

  safe_strncpy(msg.shared_lib_path, info.dli_fname, MAX_NAME_LENGTH);
  const char * symbol_name = info.dli_sname ? info.dli_sname : "__MAIN_EXECUTABLE__";
  safe_strncpy(msg.symbol_name, symbol_name, MAX_NAME_LENGTH);

  msg.fn_offset = reinterpret_cast<uintptr_t>(fn_current) - base_addr;
  msg.fn_offset_reverse = reinterpret_cast<uintptr_t>(fn_reverse) - base_addr;

  safe_strncpy(msg.args.topic_name, topic_name.c_str(), sizeof(msg.args.topic_name));
  if (cmd == BridgeCommand::CREATE_BRIDGE) {
    msg.args.qos = flatten_qos(qos);
  }

  // 2. Local MQ (Generator for THIS process) へ送信
  const std::string mq_name_str = create_mq_name_for_bridge_parent(getpid());
  mqd_t mq = mq_open(mq_name_str.c_str(), O_WRONLY);

  if (mq == (mqd_t)-1) {
    // 起動直後はまだGeneratorが準備できていない可能性があるためエラーログは出さない
    return;
  }

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) < 0) {
    RCLCPP_ERROR(logger, "mq_send failed: %s", strerror(errno));
  }
  mq_close(mq);
}

}  // namespace agnocast
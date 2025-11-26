#pragma once

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <mqueue.h>

#include <regex>

namespace agnocast

{

template <typename MessageT>
void send_bridge_request(const std::string & topic_name, const rclcpp::QoS & qos);

struct DefaultBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    send_bridge_request<MessageT>(topic_name, qos);
  }
};

struct NoBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string &, const rclcpp::QoS &)
  {
  }
};

template <typename MessageT>
class BridgeNode : public rclcpp::Node
{
private:
  using AgnoPub = agnocast::BasicPublisher<MessageT, NoBridgeRequestPolicy>;
  using AgnoSub = agnocast::BasicSubscription<MessageT, NoBridgeRequestPolicy>;
  using RosSubPtr = typename rclcpp::Subscription<MessageT>::SharedPtr;
  using RosPubPtr = typename rclcpp::Publisher<MessageT>::SharedPtr;

  const rclcpp::QoS pub_qos_;
  const rclcpp::QoS sub_qos_;

  RosPubPtr ros_pub_;
  typename AgnoPub::SharedPtr agnocast_pub_;

  RosSubPtr ros_sub_;
  typename AgnoSub::SharedPtr agnocast_sub_;

  static std::string create_node_name(const std::string & topic_name)
  {
    static const std::regex re("/");
    return "agnocast_bridge" + std::regex_replace(topic_name, re, "_");
  }

  void forward_to_agnocast(const typename MessageT::ConstSharedPtr ros_msg)
  {
    auto loaned_msg = this->agnocast_pub_->borrow_loaned_message();
    *loaned_msg = *ros_msg;
    this->agnocast_pub_->publish(std::move(loaned_msg));
  }

  void forward_to_ros(const agnocast::ipc_shared_ptr<MessageT> agno_msg)
  {
    if (this->ros_pub_->get_subscription_count() == 0) {
      return;
    }
    auto loaned_msg = this->ros_pub_->borrow_loaned_message();
    loaned_msg.get() = *agno_msg;
    this->ros_pub_->publish(std::move(loaned_msg));
  }

public:
  explicit BridgeNode(const std::string & topic_name)
  : rclcpp::Node(create_node_name(topic_name)),
    pub_qos_(rclcpp::QoS(10).reliable().transient_local()),
    sub_qos_(rclcpp::SensorDataQoS().keep_last(10)),
    ros_pub_(this->create_publisher<MessageT>(topic_name, pub_qos_)),
    agnocast_pub_(
      std::make_shared<AgnoPub>(this, topic_name, pub_qos_, agnocast::PublisherOptions{}))
  {
    rclcpp::SubscriptionOptions ros_opts;
    ros_opts.ignore_local_publications = true;

    ros_sub_ = this->create_subscription<MessageT>(
      topic_name, sub_qos_,
      [this](const typename MessageT::ConstSharedPtr msg) { this->forward_to_agnocast(msg); },
      ros_opts);

    agnocast::SubscriptionOptions agno_opts;
    // Ignore local publications to avoid message loopback.
    agno_opts.ignore_local_publications = true;

    agnocast_sub_ = std::make_shared<AgnoSub>(
      this, topic_name, sub_qos_,
      [this](const agnocast::ipc_shared_ptr<MessageT> msg) { this->forward_to_ros(msg); },
      agno_opts);
  }
};

template <typename MessageT>
std::shared_ptr<rclcpp::Node> start_bridge_node(const BridgeArgs & args)
{
  return std::make_shared<BridgeNode<MessageT>>(args.topic_name);
}

template <typename MessageT>
MqMsgBridge build_bridge_request_message(const std::string & topic_name, const rclcpp::QoS & qos)
{
  BridgeFn fn = &start_bridge_node<MessageT>;

  Dl_info info{};
  if (dladdr(reinterpret_cast<void *>(fn), &info) == 0) {
    throw std::runtime_error("dladdr failed");
  }

  MqMsgBridge msg = {};

  safe_strncpy(msg.shared_lib_path, info.dli_fname, MAX_NAME_LENGTH);
  const char * symbol_name = info.dli_sname ? info.dli_sname : "__MAIN_EXECUTABLE__";
  safe_strncpy(msg.symbol_name, symbol_name, MAX_NAME_LENGTH);
  msg.fn_ptr = reinterpret_cast<uintptr_t>(fn);

  safe_strncpy(msg.args.topic_name, topic_name.c_str(), sizeof(msg.args.topic_name));
  msg.args.qos = flatten_qos(qos);

  return msg;
}

template <typename MessageT>
void send_bridge_request(const std::string & topic_name, const rclcpp::QoS & qos)
{
  auto logger = rclcpp::get_logger("agnocast_bridge_requester");

  MqMsgBridge msg;
  try {
    msg = build_bridge_request_message<MessageT>(topic_name, qos);
  } catch (const std::runtime_error & e) {
    RCLCPP_ERROR(logger, "Failed to build bridge request message: %s", e.what());
    return;
  }

  const std::string mq_name_str = create_mq_name_for_bridge(getpid());
  const char * mq_name = mq_name_str.c_str();
  mqd_t mq = mq_open(mq_name, O_WRONLY);

  if (mq == (mqd_t)-1) {
    RCLCPP_ERROR(
      logger, "Failed to open bridge manager message queue '%s'. Error: %s", mq_name,
      strerror(errno));
    return;
  }

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) == -1) {
    RCLCPP_ERROR(
      logger, "Failed to send bridge request via mq '%s'. Error: %s", mq_name, strerror(errno));
  }

  mq_close(mq);
}

}  // namespace agnocast

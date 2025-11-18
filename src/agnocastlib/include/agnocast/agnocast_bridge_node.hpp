#pragma once

#include "agnocast/agnocast_bridge_common.hpp"
#include "agnocast/agnocast_bridge_util.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <errno.h>
#include <mqueue.h>
#include <string.h>

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

    agnocast_pub_ = std::make_shared<agnocast::BasicPublisher<MessageT, NoBridgeRequestPolicy>>(
      this, topic_name, qos, pub_options);

    auto callback = [this](const typename MessageT::ConstSharedPtr msg) {
      auto loaned_msg = this->agnocast_pub_->borrow_loaned_message();
      *loaned_msg = *msg;
      this->agnocast_pub_->publish(std::move(loaned_msg));
    };

    rclcpp::SubscriptionOptions sub_options;
    sub_options.ignore_local_publications = true;
    ros_sub_ = this->create_subscription<MessageT>(topic_name, qos, callback, sub_options);

    ros_pub_ = this->create_publisher<MessageT>(topic_name, qos);

    auto agnocast_callback = [this](const agnocast::ipc_shared_ptr<MessageT> msg) {
      auto loaned_msg = this->ros_pub_->borrow_loaned_message();
      loaned_msg.get() = *msg;
      this->ros_pub_->publish(std::move(loaned_msg));
    };

    agnocast::SubscriptionOptions agnocast_sub_options;
    agnocast_sub_options.send_r2a_bridge_request = false;

    agnocast_sub_ = std::make_shared<agnocast::BasicSubscription<MessageT, NoBridgeRequestPolicy>>(
      this, topic_name, qos, agnocast_callback, agnocast_sub_options);
  }

private:
  typename agnocast::BasicPublisher<MessageT, NoBridgeRequestPolicy>::SharedPtr agnocast_pub_;
  typename rclcpp::Subscription<MessageT>::SharedPtr ros_sub_;

  typename rclcpp::Publisher<MessageT>::SharedPtr ros_pub_;
  typename agnocast::BasicSubscription<MessageT, NoBridgeRequestPolicy>::SharedPtr agnocast_sub_;
};

template <typename MessageT>
std::shared_ptr<rclcpp::Node> start_bridge_node(const BridgeArgs & args)
{
  return std::make_shared<BridgeNode<MessageT>>(args);
}

template <typename MessageT>
void send_bridge_request(const std::string & topic_name, const rclcpp::QoS & qos)
{
  (void)qos;
  auto logger = rclcpp::get_logger("agnocast_bridge_requester");

  const std::string mq_name_str = create_mq_name_for_bridge();
  const char * mq_name = mq_name_str.c_str();
  mqd_t mq = mq_open(mq_name, O_WRONLY);

  if (mq == (mqd_t)-1) {
    RCLCPP_ERROR(
      logger, "Failed to open bridge manager message queue '%s'. Error: %s", mq_name,
      strerror(errno));
    return;
  }

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

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) == -1) {
    RCLCPP_ERROR(
      logger, "Failed to send bridge request via mq '%s'. Error: %s", mq_name, strerror(errno));
  }

  mq_close(mq);
}

struct DefaultBridgeRequestPolicy
{
  template <typename MessageT>
  static void request_bridge(const std::string & topic_name, const rclcpp::QoS & qos)
  {
    send_bridge_request<MessageT>(topic_name, qos);
  }
};

}  // namespace agnocast

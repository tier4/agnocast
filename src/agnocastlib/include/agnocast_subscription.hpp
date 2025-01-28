#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_topic_info.hpp"
#include "agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"
#include "tracetools/tracetools.h"

#include <fcntl.h>
#include <mqueue.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <cstring>
#include <functional>
#include <string>
#include <thread>
#include <vector>

namespace agnocast
{

void map_read_only_area(const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size);

struct SubscriptionOptions
{
  rclcpp::CallbackGroup::SharedPtr callback_group{nullptr};
};

// These are cut out of the class for information hiding.
mqd_t open_mq_for_subscription(
  const std::string & topic_name, const uint32_t subscriber_index,
  std::pair<mqd_t, std::string> & mq_subscription);
void remove_mq(const std::pair<mqd_t, std::string> & mq_subscription);
rclcpp::CallbackGroup::SharedPtr get_valid_callback_group(
  const rclcpp::node_interfaces::NodeBaseInterface::SharedPtr & node,
  const SubscriptionOptions & options);

class SubscriptionBase
{
protected:
  uint32_t index_;
  const std::string topic_name_;
  const rclcpp::QoS qos_;
  union ioctl_subscriber_args initialize(bool is_take_sub);

public:
  SubscriptionBase(rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos);
};

template <typename MessageT>
class Subscription : public SubscriptionBase
{
  std::pair<mqd_t, std::string> mq_subscription;

public:
  using SharedPtr = std::shared_ptr<Subscription<MessageT>>;

  Subscription(
    rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos,
    std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback,
    agnocast::SubscriptionOptions options)
  : SubscriptionBase(node, topic_name, qos)
  {
    union ioctl_subscriber_args subscriber_args = initialize(false);

    index_ = subscriber_args.ret_index;

    mqd_t mq = open_mq_for_subscription(topic_name_, index_, mq_subscription);
    auto node_base = node->get_node_base_interface();
    rclcpp::CallbackGroup::SharedPtr callback_group = get_valid_callback_group(node_base, options);

    // cppcheck-suppress unreadVariable
    uint32_t local_topic_id = agnocast::register_callback(
      callback, topic_name_, index_, static_cast<uint32_t>(qos.depth()), mq, callback_group);

#ifdef TRACETOOLS_LTTNG_ENABLED
    uint64_t pid_ltid = (static_cast<uint64_t>(subscriber_pid_) << 32) | local_topic_id;
    TRACEPOINT(
      agnocast_subscription_init, static_cast<const void *>(this),
      static_cast<const void *>(node_base->get_shared_rcl_node_handle().get()),
      static_cast<const void *>(&callback), static_cast<const void *>(callback_group.get()),
      tracetools::get_symbol(callback), topic_name.c_str(), qos.depth(), pid_ltid);
#endif

    // If there are messages available and the transient local is enabled, immediately call the
    // callback.
    if (qos_.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
      // old messages first
      for (int i = subscriber_args.ret_transient_local_num - 1; i >= 0; i--) {
        MessageT * ptr = reinterpret_cast<MessageT *>(subscriber_args.ret_last_msg_addrs[i]);
        agnocast::ipc_shared_ptr<MessageT> agnocast_ptr = agnocast::ipc_shared_ptr<MessageT>(
          ptr, topic_name_, subscriber_args.ret_publisher_indexes[i], index_,
          subscriber_args.ret_timestamps[i]);
        callback(agnocast_ptr);
      }
    }
  }

  ~Subscription() { remove_mq(mq_subscription); }
};

template <typename MessageT>
class TakeSubscription : public SubscriptionBase
{
public:
  using SharedPtr = std::shared_ptr<TakeSubscription<MessageT>>;

  TakeSubscription(rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
  : SubscriptionBase(node, topic_name, qos)
  {
#ifdef TRACETOOLS_LTTNG_ENABLED
    auto dummy_cbg = node->get_node_base_interface()->create_callback_group(
      rclcpp::CallbackGroupType::MutuallyExclusive, false);
    auto dummy_cb = []() {};
    std::string dummy_cb_symbols = "dummy_take" + topic_name;
    TRACEPOINT(
      agnocast_subscription_init, static_cast<const void *>(this),
      static_cast<const void *>(
        node->get_node_base_interface()->get_shared_rcl_node_handle().get()),
      static_cast<const void *>(&dummy_cb), static_cast<const void *>(dummy_cbg.get()),
      dummy_cb_symbols.c_str(), topic_name.c_str(), qos.depth(), 0);
#endif

    if (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
      RCLCPP_WARN(
        logger, "The transient local is not supported by TakeSubscription, so it is ignored.");
    }

    union ioctl_subscriber_args subscriber_args = initialize(true);

    index_ = subscriber_args.ret_index;
  }

  agnocast::ipc_shared_ptr<MessageT> take(bool allow_same_message = false)
  {
    union ioctl_take_msg_args take_args;
    take_args.topic_name = topic_name_.c_str();
    take_args.subscriber_index = index_;
    take_args.qos_depth = static_cast<uint32_t>(qos_.depth());
    take_args.allow_same_message = allow_same_message;
    if (ioctl(agnocast_fd, AGNOCAST_TAKE_MSG_CMD, &take_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_TAKE_MSG_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (take_args.ret_addr == 0) {
      return agnocast::ipc_shared_ptr<MessageT>();
    }

#ifdef TRACETOOLS_LTTNG_ENABLED
    TRACEPOINT(
      agnocast_take, static_cast<void *>(this), reinterpret_cast<void *>(take_args.ret_addr),
      take_args.ret_timestamp);
#endif

    MessageT * ptr = reinterpret_cast<MessageT *>(take_args.ret_addr);
    return agnocast::ipc_shared_ptr<MessageT>(
      ptr, topic_name_, take_args.ret_publisher_index, index_, take_args.ret_timestamp);
  }
};

// Wrapper of TakeSubscription for Autoware
template <typename MessageT>
class PollingSubscriber
{
  typename TakeSubscription<MessageT>::SharedPtr subscriber_;

public:
  using SharedPtr = std::shared_ptr<PollingSubscriber<MessageT>>;

  explicit PollingSubscriber(
    rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos = rclcpp::QoS{1})
  {
    subscriber_ = std::make_shared<TakeSubscription<MessageT>>(node, topic_name, qos);
  };

  const agnocast::ipc_shared_ptr<MessageT> takeData() { return subscriber_->take(true); };
};

}  // namespace agnocast

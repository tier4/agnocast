#pragma once

#include "agnocast/agnocast_callback_info.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/agnocast_tracepoint_wrapper.h"
#include "agnocast/agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

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

extern std::mutex mmap_mtx;

void map_read_only_area(const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size);

struct SubscriptionOptions
{
  rclcpp::CallbackGroup::SharedPtr callback_group{nullptr};
};

// These are cut out of the class for information hiding.
mqd_t open_mq_for_subscription(
  const std::string & topic_name, const topic_local_id_t subscriber_id,
  std::pair<mqd_t, std::string> & mq_subscription);
void remove_mq(const std::pair<mqd_t, std::string> & mq_subscription);
rclcpp::CallbackGroup::SharedPtr get_valid_callback_group(
  const rclcpp::node_interfaces::NodeBaseInterface::SharedPtr & node,
  const SubscriptionOptions & options);

class SubscriptionBase
{
protected:
  topic_local_id_t id_;
  const std::string topic_name_;
  union ioctl_add_subscriber_args initialize(
    const rclcpp::QoS & qos, const bool is_take_sub, const std::string & node_name);

public:
  SubscriptionBase(rclcpp::Node * node, const std::string & topic_name);
};

template <typename MessageT>
class Subscription : public SubscriptionBase
{
  std::pair<mqd_t, std::string> mq_subscription_;

public:
  using SharedPtr = std::shared_ptr<Subscription<MessageT>>;

  template <typename Func>
  Subscription(
    rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos, Func && callback,
    agnocast::SubscriptionOptions options)
  : SubscriptionBase(node, topic_name)
  {
    union ioctl_add_subscriber_args add_subscriber_args =
      initialize(qos, false, node->get_fully_qualified_name());

    id_ = add_subscriber_args.ret_id;

    mqd_t mq = open_mq_for_subscription(topic_name_, id_, mq_subscription_);
    auto node_base = node->get_node_base_interface();
    rclcpp::CallbackGroup::SharedPtr callback_group = get_valid_callback_group(node_base, options);

    const bool is_transient_local = qos.durability() == rclcpp::DurabilityPolicy::TransientLocal;
    [[maybe_unused]] uint32_t callback_info_id = agnocast::register_callback<MessageT>(
      std::forward<Func>(callback), topic_name_, id_, is_transient_local, mq, callback_group);

    {
      uint64_t pid_ciid = (static_cast<uint64_t>(getpid()) << 32) | callback_info_id;
      TRACEPOINT(
        agnocast_subscription_init, static_cast<const void *>(this),
        static_cast<const void *>(node_base->get_shared_rcl_node_handle().get()),
        static_cast<const void *>(&callback), static_cast<const void *>(callback_group.get()),
        tracetools::get_symbol(callback), topic_name_.c_str(), qos.depth(), pid_ciid);
    }
  }

  ~Subscription() { remove_mq(mq_subscription_); }
};

template <typename MessageT>
class TakeSubscription : public SubscriptionBase
{
public:
  using SharedPtr = std::shared_ptr<TakeSubscription<MessageT>>;

  TakeSubscription(rclcpp::Node * node, const std::string & topic_name, const rclcpp::QoS & qos)
  : SubscriptionBase(node, topic_name)
  {
    {
      auto dummy_cbg = node->get_node_base_interface()->create_callback_group(
        rclcpp::CallbackGroupType::MutuallyExclusive, false);
      auto dummy_cb = []() {};
      std::string dummy_cb_symbols = "dummy_take" + topic_name;
      TRACEPOINT(
        agnocast_subscription_init, static_cast<const void *>(this),
        static_cast<const void *>(
          node->get_node_base_interface()->get_shared_rcl_node_handle().get()),
        static_cast<const void *>(&dummy_cb), static_cast<const void *>(dummy_cbg.get()),
        dummy_cb_symbols.c_str(), topic_name_.c_str(), qos.depth(), 0);
    }

    union ioctl_add_subscriber_args add_subscriber_args =
      initialize(qos, true, node->get_fully_qualified_name());

    id_ = add_subscriber_args.ret_id;
  }

  agnocast::ipc_shared_ptr<const MessageT> take(bool allow_same_message = false)
  {
    union ioctl_take_msg_args take_args;
    take_args.topic_name = {topic_name_.c_str(), topic_name_.size()};
    take_args.subscriber_id = id_;
    take_args.allow_same_message = allow_same_message;

    {
      std::lock_guard<std::mutex> lock(mmap_mtx);

      if (ioctl(agnocast_fd, AGNOCAST_TAKE_MSG_CMD, &take_args) < 0) {
        RCLCPP_ERROR(logger, "AGNOCAST_TAKE_MSG_CMD failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      for (uint32_t i = 0; i < take_args.ret_pub_shm_info.publisher_num; i++) {
        const pid_t pid = take_args.ret_pub_shm_info.publisher_pids[i];
        const uint64_t addr = take_args.ret_pub_shm_info.shm_addrs[i];
        const uint64_t size = take_args.ret_pub_shm_info.shm_sizes[i];
        map_read_only_area(pid, addr, size);
      }
    }

    if (take_args.ret_addr == 0) {
      return agnocast::ipc_shared_ptr<const MessageT>();
    }

    TRACEPOINT(
      agnocast_take, static_cast<void *>(this), reinterpret_cast<void *>(take_args.ret_addr),
      take_args.ret_entry_id);

    MessageT * ptr = reinterpret_cast<MessageT *>(take_args.ret_addr);
    return agnocast::ipc_shared_ptr<const MessageT>(ptr, topic_name_, id_, take_args.ret_entry_id);
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

  // `takeData()` is remaining for backward compatibility.
  const agnocast::ipc_shared_ptr<const MessageT> takeData() { return subscriber_->take(true); };
  const agnocast::ipc_shared_ptr<const MessageT> take_data() { return subscriber_->take(true); };
};

}  // namespace agnocast

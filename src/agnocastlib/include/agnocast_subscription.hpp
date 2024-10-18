#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <stdio.h>
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

extern std::vector<std::thread> threads;
extern std::atomic<bool> is_running;

void map_read_only_area(const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size);

// These are cut out of the class for information hiding.
void open_mq_for_subscription(
  const std::string & topic_name, pid_t subscriber_pid,
  std::pair<mqd_t, std::string> & mq_subscription);
void remove_mq(const std::pair<mqd_t, std::string> & mq_subscription);

struct SubscriptionOptions
{
  rclcpp::CallbackGroup::SharedPtr callback_group{nullptr};
};

class SubscriptionBase
{
private:
  void wait_for_new_publisher(const pid_t subscriber_pid);

protected:
  const pid_t subscriber_pid_;
  const std::string topic_name_;
  const rclcpp::QoS qos_;

public:
  SubscriptionBase(
    const pid_t subscriber_pid, const std::string & topic_name, const rclcpp::QoS & qos);
  union ioctl_subscriber_args initialize(bool is_take_sub);
};

template <typename MessageT>
class Subscription : public SubscriptionBase
{
  std::pair<mqd_t, std::string> mq_subscription;
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr ros2_node_base_;

public:
  using SharedPtr = std::shared_ptr<Subscription<MessageT>>;

  Subscription(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node, const std::string & topic_name,
    const rclcpp::QoS & qos,
    std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback,
    agnocast::SubscriptionOptions options)
  : SubscriptionBase(getpid(), topic_name, qos), ros2_node_base_(node)
  {
    rclcpp::CallbackGroup::SharedPtr callback_group = options.callback_group;

    if (ros2_node_base_ != nullptr /* for backward compatibility */) {
      if (callback_group) {
        if (!ros2_node_base_->callback_group_in_node(callback_group)) {
          RCLCPP_ERROR(logger, "Cannot create agnocast subscription, callback group not in node.");
          close(agnocast_fd);
          exit(EXIT_FAILURE);
        }
      } else {
        callback_group = ros2_node_base_->get_default_callback_group();
      }
    }

    // To use callback_group for Agnocast Executors
    // cppcheck-suppress unusedVariable
    (void)callback_group;

    union ioctl_subscriber_args subscriber_args = initialize(false);
    open_mq_for_subscription(topic_name, subscriber_pid_, mq_subscription);

    // Create a thread that handles the messages to execute the callback
    auto th = std::thread([=]() {
      // If there are messages available and the transient local is enabled, immediately call the
      // callback.
      if (qos_.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
        // old messages first
        for (int i = subscriber_args.ret_transient_local_num - 1; i >= 0; i--) {
          MessageT * ptr = reinterpret_cast<MessageT *>(subscriber_args.ret_last_msg_addrs[i]);
          agnocast::ipc_shared_ptr<MessageT> agnocast_ptr = agnocast::ipc_shared_ptr<MessageT>(
            ptr, topic_name_, subscriber_args.ret_publisher_pids[i],
            subscriber_args.ret_timestamps[i], true);
          callback(agnocast_ptr);
        }
      }

      MqMsgAgnocast mq_msg;

      while (is_running) {
        union ioctl_receive_msg_args receive_args;
        receive_args.topic_name = topic_name_.c_str();
        receive_args.subscriber_pid = subscriber_pid_;
        receive_args.qos_depth = static_cast<uint32_t>(qos_.depth());
        if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
          RCLCPP_ERROR(logger, "AGNOCAST_RECEIVE_MSG_CMD failed: %s", strerror(errno));
          close(agnocast_fd);
          exit(EXIT_FAILURE);
        }

        for (int32_t i = (int32_t)receive_args.ret_len - 1; i >= 0; i--) {  // older messages first
          MessageT * ptr = reinterpret_cast<MessageT *>(receive_args.ret_last_msg_addrs[i]);
          agnocast::ipc_shared_ptr<MessageT> agnocast_ptr = agnocast::ipc_shared_ptr<MessageT>(
            ptr, topic_name_, receive_args.ret_publisher_pids[i], receive_args.ret_timestamps[i],
            true);
          callback(agnocast_ptr);
        }

        auto ret = mq_receive(
          mq_subscription.first, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), NULL);
        if (ret == -1) {
          RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
          return;
        }
      }
    });

    threads.push_back(std::move(th));
  }

  ~Subscription() { remove_mq(mq_subscription); }
};

template <typename MessageT>
class TakeSubscription : public SubscriptionBase
{
public:
  using SharedPtr = std::shared_ptr<TakeSubscription<MessageT>>;

  TakeSubscription(const std::string & topic_name, const rclcpp::QoS & qos)
  : SubscriptionBase(getpid(), topic_name, qos)
  {
    if (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
      RCLCPP_WARN(
        logger, "The transient local is not supported by TakeSubscription, so it is ignored.");
    }

    initialize(true);
  }

  agnocast::ipc_shared_ptr<MessageT> take()
  {
    union ioctl_take_msg_args take_args;
    take_args.topic_name = topic_name_.c_str();
    take_args.subscriber_pid = subscriber_pid_;
    take_args.qos_depth = static_cast<uint32_t>(qos_.depth());
    if (ioctl(agnocast_fd, AGNOCAST_TAKE_MSG_CMD, &take_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_TAKE_MSG_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (take_args.ret_addr == 0) {
      return agnocast::ipc_shared_ptr<MessageT>();
    }

    MessageT * ptr = reinterpret_cast<MessageT *>(take_args.ret_addr);
    return agnocast::ipc_shared_ptr<MessageT>(
      ptr, topic_name_, take_args.ret_publisher_pid, take_args.ret_timestamp, true);
  }
};

// Wrapper of TakeSubscription for Autoware
template <typename MessageT>
class PollingSubscriber
{
  typename TakeSubscription<MessageT>::SharedPtr subscriber_;
  agnocast::ipc_shared_ptr<MessageT> data_;

public:
  using SharedPtr = std::shared_ptr<PollingSubscriber<MessageT>>;

  explicit PollingSubscriber(
    const std::string & topic_name, const rclcpp::QoS & qos = rclcpp::QoS{1})
  : data_(agnocast::ipc_shared_ptr<MessageT>())
  {
    subscriber_ = std::make_shared<TakeSubscription<MessageT>>(topic_name, qos);
  };

  const agnocast::ipc_shared_ptr<MessageT> takeData()
  {
    agnocast::ipc_shared_ptr<MessageT> new_data = subscriber_->take();
    if (new_data) {
      data_ = std::move(new_data);
    }
    return data_;
  };
};

}  // namespace agnocast

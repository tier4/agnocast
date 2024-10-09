#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_logger.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
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
void wait_for_new_publisher(const uint32_t pid);
void validate_ld_preload();

std::string create_mq_name(const std::string & topic_name, const uint32_t pid);

class SubscriptionBase
{
protected:
  const pid_t subscriber_pid_;
  const std::string topic_name_;
  const rclcpp::QoS qos_;

public:
  SubscriptionBase(
    const pid_t subscriber_pid, const std::string & topic_name, const rclcpp::QoS & qos)
  : subscriber_pid_(subscriber_pid), topic_name_(topic_name), qos_(qos)
  {
    validate_ld_preload();
  }

  union ioctl_subscriber_args initialize(bool is_take_sub)
  {
    // Open a mq for new publisher appearences.
    wait_for_new_publisher(subscriber_pid_);

    // Register topic and subscriber info with the kernel module, and receive the publisher's shared
    // memory information along with messages needed to achieve transient local, if neccessary.
    union ioctl_subscriber_args subscriber_args;
    subscriber_args.topic_name = topic_name_.c_str();
    subscriber_args.qos_depth = (qos_.durability() == rclcpp::DurabilityPolicy::TransientLocal)
                                  ? static_cast<uint32_t>(qos_.depth())
                                  : 0;
    subscriber_args.subscriber_pid = subscriber_pid_;
    subscriber_args.init_timestamp = agnocast_get_timestamp();
    subscriber_args.is_take_sub = is_take_sub;
    if (ioctl(agnocast_fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &subscriber_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_SUBSCRIBER_ADD_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    for (uint32_t i = 0; i < subscriber_args.ret_publisher_num; i++) {
      if ((pid_t)subscriber_args.ret_pids[i] == subscriber_pid_) {
        /*
         * NOTE: In ROS2, communication should work fine even if the same process exists as both a
         * publisher and a subscriber for a given topic. However, in Agnocast, to avoid applying
         * Agnocast to topic communication within a component container, the system will explicitly
         * fail with an error during initialization.
         */
        RCLCPP_ERROR(
          logger,
          "This process (pid=%d) already exists in the topic (topic_name=%s) "
          "as a publisher.",
          subscriber_pid_, topic_name_.c_str());
        exit(EXIT_FAILURE);
      }
      const uint32_t pid = subscriber_args.ret_pids[i];
      const uint64_t addr = subscriber_args.ret_shm_addrs[i];
      const uint64_t size = subscriber_args.ret_shm_sizes[i];
      map_read_only_area(pid, addr, size);
    }

    return subscriber_args;
  }
};

template <typename MessageT>
class Subscription : public SubscriptionBase
{
  std::pair<mqd_t, std::string> mq_subscription;

public:
  using SharedPtr = std::shared_ptr<Subscription<MessageT>>;

  Subscription(
    const std::string & topic_name, const rclcpp::QoS & qos,
    std::function<void(const agnocast::ipc_shared_ptr<MessageT> &)> callback)
  : SubscriptionBase(getpid(), topic_name, qos)
  {
    union ioctl_subscriber_args subscriber_args = initialize(false);

    std::string mq_name = create_mq_name(topic_name_, subscriber_pid_);
    struct mq_attr attr;
    attr.mq_flags = 0;                        // Blocking queue
    attr.mq_msgsize = sizeof(MqMsgAgnocast);  // Maximum message size
    attr.mq_curmsgs = 0;  // Number of messages currently in the queue (not set by mq_open)
    attr.mq_maxmsg = 1;

    mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, 0666, &attr);
    if (mq == -1) {
      RCLCPP_ERROR(logger, "mq_open failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
    mq_subscription = std::make_pair(mq, mq_name);

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

        auto ret = mq_receive(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), NULL);
        if (ret == -1) {
          RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
          return;
        }
      }
    });

    threads.push_back(std::move(th));
  }

  ~Subscription()
  {
    /* It's best to notify the publisher and have it call mq_close, but currently
    this is not being done. The message queue is destroyed when the publisher process exits. */
    if (mq_close(mq_subscription.first) == -1) {
      RCLCPP_ERROR(logger, "mq_close failed: %s", strerror(errno));
    }
    if (mq_unlink(mq_subscription.second.c_str()) == -1) {
      RCLCPP_ERROR(logger, "mq_unlink failed: %s", strerror(errno));
    }
  }
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

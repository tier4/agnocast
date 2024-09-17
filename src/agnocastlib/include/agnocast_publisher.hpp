#pragma once

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"
#include "agnocast_smart_pointer.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <mqueue.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstdint>
#include <cstring>

namespace agnocast
{

extern int agnocast_fd;
uint64_t agnocast_get_timestamp();

std::string create_mq_name(const std::string & topic_name, const uint32_t pid);

template <typename MessageT>
class Publisher
{
  std::string topic_name_;
  uint32_t publisher_pid_;
  rclcpp::QoS qos_;
  std::unordered_map<std::string, mqd_t>
    opened_mqs;  // TODO: The mq should be closed when a subscriber unsubscribes the topic, but this
                 // is not currently implemented.

public:
  Publisher(const std::string & topic_name, const rclcpp::QoS & qos)
  : topic_name_(topic_name), qos_(qos)
  {
    publisher_pid_ = getpid();

    union ioctl_publisher_args pub_args;
    pub_args.publisher_pid = publisher_pid_;
    pub_args.topic_name = topic_name_.c_str();
    if (ioctl(agnocast_fd, AGNOCAST_PUBLISHER_ADD_CMD, &pub_args) < 0) {
      perror("AGNOCAST_PUBLISHER_ADD_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    // Send messages to subscribers to notify that a new publisher appears
    for (uint32_t i = 0; i < pub_args.ret_subscriber_len; i++) {
      if (pub_args.ret_subscriber_pids[i] == publisher_pid_) {
        /*
         * NOTE: In ROS2, communication should work fine even if the same process exists as both a
         * publisher and a subscriber for a given topic. However, in Agnocast, to avoid applying
         * Agnocast to topic communication within a component container, the system will explicitly
         * fail with an error during initialization.
         */
        std::cout << "[Error]: This process (pid=" << publisher_pid_
                  << ") already exists in the topic (topic_name=" << topic_name
                  << ") as a subscriber." << std::endl;
        exit(EXIT_FAILURE);
      }
      const std::string mq_name =
        "/new_publisher@" + std::to_string(pub_args.ret_subscriber_pids[i]);
      mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY);
      if (mq == -1) {
        perror("mq_open for new publisher failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      MqMsgNewPublisher mq_msg;
      mq_msg.publisher_pid = publisher_pid_;
      mq_msg.shm_addr = pub_args.ret_shm_addr;
      mq_msg.shm_size = pub_args.ret_shm_size;
      if (mq_send(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), 0) == -1) {
        perror("mq_send for new publisher failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }
    }
  }

  message_ptr<MessageT> borrow_loaned_message()
  {
    MessageT * ptr = new MessageT();
    return borrow_loaned_message(ptr);
  }

  message_ptr<MessageT> borrow_loaned_message(MessageT * ptr)
  {
    uint64_t timestamp = agnocast_get_timestamp();
    union ioctl_enqueue_and_release_args ioctl_args;
    ioctl_args.topic_name = topic_name_.c_str();
    ioctl_args.publisher_pid = publisher_pid_;
    ioctl_args.qos_depth = static_cast<uint32_t>(qos_.depth());
    ioctl_args.msg_virtual_address = reinterpret_cast<uint64_t>(ptr);
    ioctl_args.timestamp = timestamp;
    if (ioctl(agnocast_fd, AGNOCAST_ENQUEUE_AND_RELEASE_CMD, &ioctl_args) < 0) {
      perror("AGNOCAST_ENQUEUE_AND_RELEASE_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    for (size_t i = 0; i < ioctl_args.ret_len; i++) {
      MessageT * release_ptr = reinterpret_cast<MessageT *>(ioctl_args.ret_released_addrs[i]);
      delete release_ptr;
    }

    return message_ptr<MessageT>(ptr, topic_name_.c_str(), publisher_pid_, timestamp, false);
  }

  void publish(message_ptr<MessageT> && message)
  {
    if (topic_name_.c_str() != message.get_topic_name()) return;  // string comparison?
    if (publisher_pid_ != message.get_publisher_pid()) return;

    union ioctl_publish_args publish_args;
    publish_args.topic_name = topic_name_.c_str();
    publish_args.publisher_pid = publisher_pid_;
    publish_args.msg_timestamp = message.get_timestamp();
    if (ioctl(agnocast_fd, AGNOCAST_PUBLISH_MSG_CMD, &publish_args) < 0) {
      perror("AGNOCAST_PUBLISH_MSG_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    for (uint32_t i = 0; i < publish_args.ret_len; i++) {
      uint32_t pid = publish_args.ret_pids[i];

      std::string mq_name = create_mq_name(topic_name_.c_str(), pid);
      mqd_t mq;
      if (opened_mqs.find(mq_name) != opened_mqs.end()) {
        mq = opened_mqs[mq_name];
      } else {
        mq = mq_open(mq_name.c_str(), O_WRONLY | O_NONBLOCK);
        if (mq == -1) {
          perror("mq_open failed");
          continue;
        }
        opened_mqs.insert({mq_name, mq});
      }

      struct MqMsgAgnocast mq_msg;
      if (mq_send(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), 0) == -1) {
        // If it returns EAGAIN, it means mq_send has already been executed, but the subscriber
        // hasn't received it yet. Thus, there's no need to send it again since the notification has
        // already been sent.
        if (errno != EAGAIN) {
          perror("mq_send failed");
        }
      }
    }
  }

  uint32_t get_subscription_count() const
  {
    union ioctl_get_subscriber_num_args get_subscriber_count_args;
    get_subscriber_count_args.topic_name = topic_name_.c_str();
    if (ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) < 0) {
      perror("AGNOCAST_GET_SUBSCRIBER_NUM_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return get_subscriber_count_args.ret_subscriber_num;
  }
};

}  // namespace agnocast

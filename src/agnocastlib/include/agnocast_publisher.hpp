#pragma once

#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <atomic>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <memory>
#include <thread>
#include <vector>
#include <chrono>
#include <sys/ioctl.h>

#include "agnocast_ioctl.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_mq.hpp"

namespace agnocast {

extern int agnocast_fd;
uint64_t agnocast_get_timestamp();

template<typename MessageT>
class Publisher {
  const char *topic_name_;
  std::string topic_name_cpp_;
  uint32_t publisher_pid_;

public:

  Publisher(std::string topic_name) {
    topic_name_cpp_ = topic_name;
    topic_name_ = topic_name_cpp_.c_str();
    publisher_pid_ = getpid();

    if (ioctl(agnocast_fd, AGNOCAST_TOPIC_ADD_CMD, topic_name_) < 0) {
        perror("Failed to execute ioctl");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }

    struct ioctl_publisher_args pub_args;
    pub_args.pid = publisher_pid_;
    pub_args.topic_name = topic_name_;
     if (ioctl(agnocast_fd, AGNOCAST_PUBLISHER_ADD_CMD, &pub_args) < 0) {
        perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }
  }

  message_ptr<MessageT> borrow_loaded_message() {
    MessageT *ptr = new MessageT();
    return borrow_loaded_message(ptr);
  }

  message_ptr<MessageT> borrow_loaded_message(MessageT *ptr) {
    union ioctl_release_oldest_args release_args;
    release_args.topic_name = topic_name_;
    release_args.publisher_pid = publisher_pid_;
    release_args.buffer_depth = 5;
    if (ioctl(agnocast_fd, AGNOCAST_RELEASE_OLDEST_CMD, &release_args) < 0) {
        perror("AGNOCAST_RELEASE_OLDEST_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }

    if (release_args.ret != 0) {
      MessageT *release_ptr = reinterpret_cast<MessageT*>(release_args.ret);
      delete release_ptr;
    }

    uint64_t timestamp = agnocast_get_timestamp();

    struct ioctl_enqueue_entry_args enqueue_args;
    enqueue_args.topic_name = topic_name_;
    enqueue_args.publisher_pid = publisher_pid_;
    enqueue_args.msg_virtual_address = reinterpret_cast<uint64_t>(ptr);
    enqueue_args.timestamp = timestamp;
    if (ioctl(agnocast_fd, AGNOCAST_ENQUEUE_ENTRY_CMD, &enqueue_args) < 0) {
        perror("AGNOCAST_ENQUEUE_ENTRY_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }

    return message_ptr<MessageT>(ptr, topic_name_, publisher_pid_, timestamp);
  }

  void publish(message_ptr<MessageT>&& message) {
    if (topic_name_ != message.get_topic_name()) return; // string comparison?
    if (publisher_pid_ != message.get_publisher_pid()) return;

    union ioctl_publish_args publish_args;
    publish_args.topic_name = topic_name_;
    publish_args.publisher_pid = publisher_pid_;
    publish_args.msg_timestamp = message.get_timestamp();
    if (ioctl(agnocast_fd, AGNOCAST_PUBLISH_MSG_CMD, &publish_args) < 0) {
        perror("AGNOCAST_PUBLISH_MSG_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }

    for (uint32_t i = 0; i < publish_args.ret_len; i++) {
      uint32_t pid = publish_args.ret_pids[i];

      std::string mq_name = std::string(topic_name_) + "|" + std::to_string(pid);
      mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY);

      if (mq == -1) {
        perror("mq_open");
        std::cerr << "mq_open error" << std::endl;
        continue;
      }

      MqMsgAgnocast mq_msg;
      mq_msg.publisher_pid = publisher_pid_;
      mq_msg.timestamp = message.get_timestamp();

      if (mq_send(mq, reinterpret_cast<char*>(&mq_msg), sizeof(mq_msg), 0) == -1) {
        perror("mq_send");
        std::cerr << "mq_send error" << std::endl;
        continue;
      }
    }
  }
};

} // namespace agnocast

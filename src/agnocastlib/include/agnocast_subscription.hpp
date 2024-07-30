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
#include <thread>
#include <vector>
#include <sys/ioctl.h>
#include <stdio.h>

#include "rclcpp/rclcpp.hpp"

#include "agnocast_ioctl.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_mq.hpp"

namespace agnocast {

extern std::vector<std::thread> threads;
extern std::atomic<bool> is_running;

void map_rdonly_area(const uint32_t pid, const uint64_t addr);
void map_rdonly_areas(const char* topic_name);
size_t read_mq_msgmax();
void wait_for_new_publisher(const uint32_t pid);

std::string create_mq_name(const char* topic_name, const uint32_t pid);

template<typename MessageT> class Subscription {
  std::pair<mqd_t, std::string> mq_subscription;

public:

  Subscription(const char* topic_name, const rclcpp::QoS& qos, std::function<void(const agnocast::message_ptr<MessageT> &)> callback) {
    union ioctl_add_topic_sub_args add_topic_args;
    add_topic_args.topic_name = topic_name;
    add_topic_args.qos_depth = (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) ? static_cast<uint32_t>(qos.depth()) : 0;
    if (ioctl(agnocast_fd, AGNOCAST_TOPIC_ADD_SUB_CMD, &add_topic_args) < 0) {
        perror("AGNOCAST_TOPIC_ADD_SUB_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
    }

    const pid_t subscriber_pid = getpid();

    std::string mq_name = create_mq_name(topic_name, subscriber_pid);

    struct mq_attr attr;
    attr.mq_flags = 0; // Blocking queue
    attr.mq_msgsize = sizeof(MqMsgAgnocast); // Maximum message size
    attr.mq_curmsgs = 0; // Number of messages currently in the queue (not set by mq_open)
    /* 
    * NOTE:
    *   Maximum number of messages in the queue.
    *   mq_maxmsg is limited by /proc/sys/fs/mqueue/msg_max and defaults to 10.
    *   Although this limit can be changed by editing the file, here mq_maxmsg is used without being changed.
    *   If mq_send() is called when the message queue is full, it will block until the queue is free,
    *   so this value may need to be reconsidered in the future.
    */
    attr.mq_maxmsg = static_cast<__syscall_slong_t>(read_mq_msgmax());

    mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, 0666, &attr);
    if (mq == -1) {
      perror("mq_open failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
    mq_subscription = std::make_pair(mq, mq_name);

    struct ioctl_subscriber_args subscriber_args;
    subscriber_args.pid = subscriber_pid;
    subscriber_args.topic_name = topic_name;
    if (ioctl(agnocast_fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &subscriber_args) < 0) {
      perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    map_rdonly_areas(topic_name);

    // Create a thread that handles the messages to execute the callback
    auto th = std::thread([=]() {
      std::cout << "callback thread for " << topic_name << " has been started" << std::endl;

      // If there are messages available and the transient local is enabled, immediately call the callback.
      if (qos.durability() == rclcpp::DurabilityPolicy::TransientLocal) {
        for (int i = 0; i < add_topic_args.ret_len; i++) {
          MessageT* ptr = reinterpret_cast<MessageT*>(add_topic_args.ret_last_msg_addrs[i]);
          agnocast::message_ptr<MessageT> agnocast_ptr = agnocast::message_ptr<MessageT>(ptr, topic_name, add_topic_args.ret_publisher_pids[i], add_topic_args.ret_timestamps[i], true);
          callback(agnocast_ptr);
        }
      }

      MqMsgAgnocast mq_msg;

      while (is_running) {
        auto ret = mq_receive(mq, reinterpret_cast<char*>(&mq_msg), sizeof(mq_msg), NULL);
        if (ret == -1) {
          perror("mq_receive failed");
          return;
        }

        union ioctl_receive_msg_args receive_args;
        receive_args.topic_name = topic_name;
        receive_args.publisher_pid = mq_msg.publisher_pid;
        receive_args.msg_timestamp = mq_msg.timestamp;
        receive_args.qos_depth = static_cast<uint32_t>(qos.depth());
        if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
          perror("AGNOCAST_RECEIVE_MSG_CMD failed");
          close(agnocast_fd);
          exit(EXIT_FAILURE);
        }

        if (receive_args.ret == 0) {  // Number of messages > qos_depth
          continue;
        }

        MessageT* ptr = reinterpret_cast<MessageT*>(receive_args.ret); 
        agnocast::message_ptr<MessageT> agnocast_ptr = agnocast::message_ptr<MessageT>(ptr, topic_name, mq_msg.publisher_pid, mq_msg.timestamp, true);

        /*
        if (subscriber_pid == mq_msg.publisher_pid) {
          return;
        }
        */

        callback(agnocast_ptr);
      }
    });

    threads.push_back(std::move(th));
  }

  ~Subscription(){
    /* It's best to notify the publisher and have it call mq_close, but currently 
    this is not being done. The message queue is destroyed when the publisher process exits. */
    if (mq_close(mq_subscription.first) == -1){
      perror("mq_close failed");
    }
    if (mq_unlink(mq_subscription.second.c_str()) == -1){
      perror("mq_unlink failed");
    }
  }
};
                        
} // namespace agnocast

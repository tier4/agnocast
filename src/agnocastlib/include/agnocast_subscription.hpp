#pragma once

#include <cstddef>
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

#include "agnocast_ioctl.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_mq.hpp"

namespace agnocast {

extern std::vector<std::thread> threads;
extern std::atomic<bool> is_running;

void map_rdonly_area(uint32_t pid, uint64_t addr);
void map_rdonly_areas(const char* topic_name);

template<typename MessageT> class Subscription { };

mqd_t initialize_mq(const std::string &mq_name, const size_t size) {
  struct mq_attr attr;
  attr.mq_flags = 0; // Blocking queue
  attr.mq_maxmsg = 10; // Maximum number of messages in the queue
  attr.mq_msgsize = size; // Maximum message size
  attr.mq_curmsgs = 0; // Number of messages currently in the queue (not set by mq_open)

  mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, 0666, &attr);
  if (mq == -1) {
    perror("mq_open for new publisher failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return mq;
}

void wait_new_publisher(const mqd_t &mq) {
  MqMsgNewPublisher mq_msg;

  while (is_running) {
    auto ret = mq_receive(mq, reinterpret_cast<char*>(&mq_msg), sizeof(mq_msg), NULL);
    if (ret == -1) {
      perror("mq_receive for new publisher failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    uint32_t publisher_pid = mq_msg.publisher_pid;
    uint64_t publisher_shm_addr = mq_msg.shm_addr;
    map_rdonly_area(publisher_pid, publisher_shm_addr);
  }
}

template<typename T>
void subscribe_topic_agnocast(const char* topic_name, std::function<void(const agnocast::message_ptr<T> &)> callback) {
  if (ioctl(agnocast_fd, AGNOCAST_TOPIC_ADD_CMD, topic_name) < 0) {
      perror("AGNOCAST_TOPIC_ADD_CMD failed");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
  }

  mqd_t mq_for_new_publisher = initialize_mq(std::string(topic_name) + "_" + std::to_string(getpid()), sizeof(MqMsgNewPublisher));
  mqd_t mq_for_topic_publish = initialize_mq(std::string(topic_name) + "|" + std::to_string(getpid()), sizeof(MqMsgAgnocast));

  struct ioctl_subscriber_args subscriber_args;
  subscriber_args.pid = getpid();
  subscriber_args.topic_name = topic_name;
  if (ioctl(agnocast_fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &subscriber_args) < 0) {
    perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  map_rdonly_areas(topic_name);

  // Create a thread that maps the areas for publishers afterwards
  std::thread th_for_new_publisher(wait_new_publisher, mq_for_new_publisher);

  // Create a thread that handles the messages to execute the callback
  auto th_for_topic_publish = std::thread([=]() {
    std::cout << "callback thread for " << topic_name << " has been started" << std::endl;
    MqMsgAgnocast mq_msg;

    while (is_running) {
      auto ret = mq_receive(mq_for_topic_publish, reinterpret_cast<char*>(&mq_msg), sizeof(mq_msg), NULL);
      if (ret == -1) {
        perror("mq_receive failed");
        return;
      }

      union ioctl_update_entry_args entry_args;
      entry_args.topic_name = topic_name;
      entry_args.publisher_pid = mq_msg.publisher_pid;
      entry_args.msg_timestamp = mq_msg.timestamp;
      if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &entry_args) < 0) {
        perror("AGNOCAST_RECEIVE_MSG_CMD failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      if (entry_args.ret == 0) {
        std::cerr << "The received message has message address zero" << std::endl;
        continue;
      }

      T* ptr = reinterpret_cast<T*>(entry_args.ret); 
      agnocast::message_ptr<T> agnocast_ptr = agnocast::message_ptr<T>(ptr, topic_name, mq_msg.publisher_pid, mq_msg.timestamp, true);

      /*
      if (subscriber_pid == mq_msg.publisher_pid) {
        return;
      }
      */

      callback(agnocast_ptr);
    }
  });

  threads.push_back(std::move(th_for_new_publisher));
  threads.push_back(std::move(th_for_topic_publish));
}

} // namespace agnocast

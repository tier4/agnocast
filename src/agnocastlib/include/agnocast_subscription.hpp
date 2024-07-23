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

#include "agnocast_ioctl.hpp"
#include "agnocast_smart_pointer.hpp"
#include "agnocast_mq.hpp"
#include "preloaded.hpp"

namespace agnocast {

extern std::vector<std::thread> threads;
extern std::atomic<bool> is_running;

template<typename MessageT> class Subscription { };

template<typename T>
void subscribe_topic_agnocast(const char* topic_name, std::function<void(const agnocast::message_ptr<T> &)> callback) {
  if (ioctl(agnocast_fd, AGNOCAST_TOPIC_ADD_CMD, topic_name) < 0) {
      perror("Failed to execute ioctl");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
  }

  uint32_t subscriber_pid = getpid();

  std::string mq_name = std::string(topic_name) + "|" + std::to_string(getpid());
  mqd_t mq = mq_open(mq_name.c_str(), O_RDONLY);

  if (mq == -1) {
    std::cout << "create agnocast topic mq: " << mq_name << std::endl;

    struct mq_attr attr;
    attr.mq_flags = 0; // Blocking queue
    attr.mq_maxmsg = 10; // Maximum number of messages in the queue
    attr.mq_msgsize = sizeof(MqMsgAgnocast); // Maximum message size
    attr.mq_curmsgs = 0; // Number of messages currently in the queue (not set by mq_open)

    mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, 0666, &attr);
    if (mq == -1) {
      perror("mq_open");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  }

  struct ioctl_subscriber_args subscriber_args;
  subscriber_args.pid = subscriber_pid;
  subscriber_args.topic_name = topic_name;
  if (ioctl(agnocast_fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &subscriber_args) < 0) {
    perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // get shared memory info from topic_name from kernel module
  union ioctl_get_shm_args get_shm_args;
  get_shm_args.topic_name = topic_name;
  if (ioctl(agnocast_fd, AGNOCAST_GET_SHM_CMD, &get_shm_args) < 0) {
    perror("AGNOCAST_GET_SHM_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // map read-only shared memory through heaphook
  for (uint32_t i = 0; i < get_shm_args.ret_publisher_num; i++) {
    uint32_t pid = get_shm_args.ret_pids[i];
    uint64_t addr = get_shm_args.ret_addrs[i];
    char shm_name[20]; // enough size for pid
    sprintf(shm_name,"%d", pid);
    map_area(shm_name, addr, false);
  }

  // Create a thread that handles the messages to execute the callback
  auto th = std::thread([=]() {
    std::cout << "callback thread for " << topic_name << " has been started" << std::endl;
    MqMsgAgnocast mq_msg;

    while (is_running) {
      auto ret = mq_receive(mq, reinterpret_cast<char*>(&mq_msg), sizeof(mq_msg), NULL);

      if (ret == -1) {
        std::cerr << "mq_receive error" << std::endl;
        perror("mq_receive error");
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

  threads.push_back(std::move(th));
}

} // namespace agnocast

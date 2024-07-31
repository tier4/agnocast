#include <atomic>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <stdio.h>

#include "agnocast.hpp"
#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"
#include "preloaded.hpp"

namespace agnocast {

int agnocast_fd = -1;
std::atomic<bool> is_running = true;
std::vector<std::thread> threads;

uint64_t agnocast_get_timestamp() {
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

void map_rdonly_area(const uint32_t pid, const uint64_t addr) {
  char shm_name[20]; // enough size for pid
  sprintf(shm_name,"%d", pid);
  map_area(shm_name, addr, false);
}

void map_rdonly_areas(const char* topic_name) {
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
    const uint32_t pid = get_shm_args.ret_pids[i];
    const uint64_t addr = get_shm_args.ret_addrs[i];
    std::cout << pid << " " << addr << std::endl;
    map_rdonly_area(pid, addr);
  }
}

std::string create_mq_name(const char* topic_name, const uint32_t pid) {
  std::string mq_name = std::string(topic_name) + "@" + std::to_string(pid);

  if (mq_name[0] != '/') {
    perror("create_mq_name failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  
  // As a mq_name, '/' cannot be used
  for (size_t i = 1; i < mq_name.size(); i++) {
    if (mq_name[i] == '/') {
      mq_name[i] = '_';
    }
  }
  
  return mq_name;
}

void wait_for_new_publisher(const uint32_t pid) {
  const std::string mq_name = "/new_publisher@" + std::to_string(pid);
  
  struct mq_attr attr;
  attr.mq_flags = 0; // Blocking queue
  attr.mq_maxmsg = 10; // Maximum number of messages in the queue
  attr.mq_msgsize = sizeof(MqMsgNewPublisher); // Maximum message size
  attr.mq_curmsgs = 0; // Number of messages currently in the queue (not set by mq_open)
  
  mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, 0666, &attr);
  if (mq == -1) {
    perror("mq_open for new publisher failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // Create a thread that maps the areas for publishers afterwards
  auto th = std::thread([=]() {
    std::cout << "thread for new publisher has started" << std::endl;

    while (is_running) {
      MqMsgNewPublisher mq_msg;
      auto ret = mq_receive(mq, reinterpret_cast<char*>(&mq_msg), sizeof(mq_msg), NULL);
      if (ret == -1) {
        perror("mq_receive for new publisher failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      const uint32_t publisher_pid = mq_msg.publisher_pid;
      const uint64_t publisher_shm_addr = mq_msg.shm_addr;
      map_rdonly_area(publisher_pid, publisher_shm_addr);
    }
  });

  threads.push_back(std::move(th));
}

void initialize_agnocast() {
  if (agnocast_fd >= 0) return;

  agnocast_fd = open("/dev/agnocast", O_RDWR);
  if (agnocast_fd < 0) {
      perror("Failed to open the device");
      exit(EXIT_FAILURE);
  }

  const uint32_t pid = getpid();

  // get allocatable shared memory addr from kernel module
  union ioctl_new_shm_args new_shm_args;
  new_shm_args.pid = pid;
  if (ioctl(agnocast_fd, AGNOCAST_NEW_SHM_CMD, &new_shm_args) < 0) {
    perror("AGNOCAST_GET_SHM_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // call heaphook function
  char shm_name[20]; // enough size for pid
  sprintf(shm_name,"%d", pid);
  initialize_mempool(shm_name, new_shm_args.ret_addr);

  // open a mq for new publisher appearences
  wait_for_new_publisher(pid);
}

size_t read_mq_msgmax() {
  std::ifstream msgmax_file("/proc/sys/fs/mqueue/msg_max");
  if (!msgmax_file.is_open()) {
    perror("Opening /proc/sys/fs/mqueue/msg_max failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  size_t mq_msgmax;
  if (!(msgmax_file >> mq_msgmax)) {
    perror("Reading /proc/sys/fs/mqueue/msg_max failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  msgmax_file.close();

  return mq_msgmax;
}

static void shutdown_agnocast() {
  is_running = false;

  std::cout << "shutting down agnocast.." << std::endl;

  for (auto &th : threads) {
    th.join();
  }
}

class Cleanup {
public:
  ~Cleanup() {
    shutdown_agnocast();
  }
};

static Cleanup cleanup;

} // namespace agnocast

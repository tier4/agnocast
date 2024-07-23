#include <atomic>
#include <cstdint>
#include <iostream>
#include <stdio.h>

#include "agnocast.hpp"
#include "agnocast_ioctl.hpp"
#include "preloaded.hpp"

namespace agnocast {

int agnocast_fd = -1;
std::atomic<bool> is_running = true;
std::vector<std::thread> threads;

uint64_t agnocast_get_timestamp() {
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

void initialize_agnocast() {
  if (agnocast_fd >= 0) return;

  agnocast_fd = open("/dev/agnocast", O_RDWR);
  if (agnocast_fd < 0) {
      perror("Failed to open the device");
      exit(EXIT_FAILURE);
  }

  // get allocatable shared memory addr from kernel module
  union ioctl_new_shm_args new_shm_args;
  new_shm_args.pid = getpid();
  if (ioctl(agnocast_fd, AGNOCAST_NEW_SHM_CMD, &new_shm_args) < 0) {
    perror("AGNOCAST_GET_SHM_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // call heaphook function
  char shm_name[20]; // enough size for pid
  sprintf(shm_name,"%d", getpid());
  initialize_mempool(shm_name, new_shm_args.ret_addr);
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

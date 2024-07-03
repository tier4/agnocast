#include <atomic>
#include <map>
#include <iostream>

#include "agnocast.hpp"

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

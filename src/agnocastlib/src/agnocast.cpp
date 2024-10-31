#include "agnocast.hpp"

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"

#include <stdio.h>

#include <atomic>
#include <cstdint>
#include <fstream>
#include <set>

namespace agnocast
{

int agnocast_fd = -1;
std::atomic<bool> is_running = true;
std::vector<std::thread> threads;
std::vector<int> shm_fds;
extern mqd_t mq_new_publisher;

bool already_mapped(const uint32_t pid)
{
  static pthread_mutex_t mapped_pid_mtx = PTHREAD_MUTEX_INITIALIZER;
  static std::set<uint32_t> mapped_publisher_pids;

  pthread_mutex_lock(&mapped_pid_mtx);
  const bool inserted = mapped_publisher_pids.insert(pid).second;
  pthread_mutex_unlock(&mapped_pid_mtx);

  return !inserted;
}

void * map_area(
  const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size, const bool writable)
{
  const std::string shm_name = "/agnocast@" + std::to_string(pid);

  int oflag = writable ? O_CREAT | O_RDWR : O_RDONLY;
  int shm_fd = shm_open(shm_name.c_str(), oflag, 0666);
  if (shm_fd == -1) {
    perror("[ERROR] [Agnocast] shm_open failed");
    close(agnocast_fd);
    return NULL;
  }
  shm_fds.push_back(shm_fd);

  if (writable) {
    if (ftruncate(shm_fd, shm_size) == -1) {
      perror("[ERROR] [Agnocast] ftruncate failed");
      close(agnocast_fd);
      return NULL;
    }
  }

  int prot = writable ? PROT_READ | PROT_WRITE : PROT_READ;
  void * ret = mmap(
    reinterpret_cast<void *>(shm_addr), shm_size, prot, MAP_SHARED | MAP_FIXED_NOREPLACE, shm_fd,
    0);

  if (ret == MAP_FAILED) {
    perror("[ERROR] [Agnocast] mmap failed");
    close(agnocast_fd);
    return NULL;
  }

  return ret;
}

void * map_writable_area(const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size)
{
  if (already_mapped(pid)) {
    fprintf(stderr, "[ERROR] [Agnocast] map_writeable_area failed");
    close(agnocast_fd);
    return NULL;
  }

  return map_area(pid, shm_addr, shm_size, true);
}

void map_read_only_area(const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size)
{
  if (already_mapped(pid)) return;
  if (map_area(pid, shm_addr, shm_size, false) == NULL) exit(EXIT_FAILURE);
}

// NOTE: Do not use std::cout inside initialize_agnocast thread
void * initialize_agnocast(const uint64_t shm_size)
{
  if (agnocast_fd >= 0) {
    perror("[ERROR] [Agnocast] Agnocast is already open");
    return NULL;
  }

  agnocast_fd = open("/dev/agnocast", O_RDWR);
  if (agnocast_fd < 0) {
    perror("[ERROR] [Agnocast] Failed to open the device");
    return NULL;
  }

  const uint32_t pid = getpid();

  union ioctl_new_shm_args new_shm_args;
  new_shm_args.pid = pid;
  new_shm_args.shm_size = shm_size;
  if (ioctl(agnocast_fd, AGNOCAST_NEW_SHM_CMD, &new_shm_args) < 0) {
    perror("[ERROR] [Agnocast] AGNOCAST_NEW_SHM_CMD failed");
    close(agnocast_fd);
    return NULL;
  }
  return map_writable_area(pid, new_shm_args.ret_addr, shm_size);
}

static void shutdown_agnocast()
{
  fprintf(stdout, "[INFO] [Agnocast]: shutdown_agnocast started\n");
  is_running.store(false);
  /*
   * TODO:
   *   It might seem odd to re-acquire the PID and regenerate mq_name and shm_name.
   *   However, this approach was taken because the code that stored the `mq_name`
   *   and `shm_name` strings as global variables didn't work. The reason it didn't
   *   work is likely related to the fact that initialize_agnocast() cannot use heap
   *   memory. Once this issue is resolved, this implementation will be revised.
   */
  const uint32_t pid = getpid();

  for (int fd : shm_fds) {
    if (close(fd) == -1) {
      perror("[ERROR] [Agnocast] close shm_fd failed");
    }
  }

  const std::string shm_name = "/agnocast@" + std::to_string(pid);
  if (shm_unlink(shm_name.c_str()) == -1) {
    perror("[ERROR] [Agnocast] shm_unlink failed");
  }

  if (mq_new_publisher != -1) {
    if (mq_close(mq_new_publisher) == -1) {
      perror("[ERROR] [Agnocast] mq_close failed");
    }

    const std::string mq_name = "/new_publisher@" + std::to_string(pid);
    if (mq_unlink(mq_name.c_str()) == -1) {
      perror("[ERROR] [Agnocast] mq_unlink failed");
    }
  }

  for (auto & th : threads) {
    th.join();
  }

  fprintf(stdout, "[INFO] [Agnocast]: shutdown_agnocast completed\n");
}

class Cleanup
{
public:
  ~Cleanup() { shutdown_agnocast(); }
};

static Cleanup cleanup;

}  // namespace agnocast

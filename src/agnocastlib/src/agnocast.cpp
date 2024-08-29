#include "agnocast.hpp"

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"

#include <stdio.h>

#include <atomic>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>

namespace agnocast
{

int agnocast_fd = -1;
std::atomic<bool> is_running = true;
std::vector<std::thread> threads;
std::vector<int> shm_fds;
mqd_t mq_new_publisher;

static pthread_mutex_t wait_newpub_mtx = PTHREAD_MUTEX_INITIALIZER;

static size_t INITIAL_MEMPOOL_SIZE = 100 * 1000 * 1000;  // default: 100MB

uint64_t agnocast_get_timestamp()
{
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

// TODO: when called from initialize_agnocast(), map_area() should not exit, but return NULL
void * map_area(const uint32_t pid, const uint64_t shm_addr, const bool writable)
{
  static pthread_mutex_t mapped_pid_mtx = PTHREAD_MUTEX_INITIALIZER;
  static std::set<uint32_t> mapped_publisher_pids;

  pthread_mutex_lock(&mapped_pid_mtx);
  const bool inserted = mapped_publisher_pids.insert(pid).second;
  pthread_mutex_unlock(&mapped_pid_mtx);

  if (!inserted) return NULL;

  const std::string shm_name = "/agnocast@" + std::to_string(pid);

  int oflag = writable ? O_CREAT | O_RDWR : O_RDONLY;
  int shm_fd = shm_open(shm_name.c_str(), oflag, 0666);
  if (shm_fd == -1) {
    perror("shm_open failed");
    close(agnocast_fd);
    if (writable) return NULL;
    exit(EXIT_FAILURE);
  }
  shm_fds.push_back(shm_fd);

  if (writable) {
    if (ftruncate(shm_fd, INITIAL_MEMPOOL_SIZE) == -1) {
      perror("ftruncate failed");
      close(agnocast_fd);
      return NULL;
    }
  }

  int prot = writable ? PROT_READ | PROT_WRITE : PROT_READ;
  void * ret = mmap(
    reinterpret_cast<void *>(shm_addr), INITIAL_MEMPOOL_SIZE, prot,
    MAP_SHARED | MAP_FIXED_NOREPLACE, shm_fd, 0);

  if (ret == MAP_FAILED) {
    perror("mmap failed");
    close(agnocast_fd);
    if (writable) return NULL;
    exit(EXIT_FAILURE);
  }

  return ret;
}

std::string create_mq_name(const char * topic_name, const uint32_t pid)
{
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

void wait_for_new_publisher(const uint32_t pid)
{
  pthread_mutex_lock(&wait_newpub_mtx);

  static bool is_initialized = false;
  if (is_initialized) {
    pthread_mutex_unlock(&wait_newpub_mtx);
    return;
  }
  is_initialized = true;

  pthread_mutex_unlock(&wait_newpub_mtx);

  const std::string mq_name = "/new_publisher@" + std::to_string(pid);

  struct mq_attr attr;
  attr.mq_flags = 0;                            // Blocking queue
  attr.mq_maxmsg = 10;                          // Maximum number of messages in the queue
  attr.mq_msgsize = sizeof(MqMsgNewPublisher);  // Maximum message size
  attr.mq_curmsgs = 0;  // Number of messages currently in the queue (not set by mq_open)

  mqd_t mq = mq_open(mq_name.c_str(), O_CREAT | O_RDONLY, 0666, &attr);
  if (mq == -1) {
    perror("mq_open for new publisher failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  mq_new_publisher = mq;

  // Create a thread that maps the areas for publishers afterwards
  auto th = std::thread([=]() {
    while (is_running) {
      MqMsgNewPublisher mq_msg;
      auto ret = mq_receive(mq, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), NULL);
      if (ret == -1) {
        perror("mq_receive for new publisher failed");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      const uint32_t publisher_pid = mq_msg.publisher_pid;
      const uint64_t publisher_shm_addr = mq_msg.shm_addr;
      map_area(publisher_pid, publisher_shm_addr, false);
    }
  });

  threads.push_back(std::move(th));
}

// NOTE: Do not use std::cout inside initialize_agnocast thread
void * initialize_agnocast()
{
  if (agnocast_fd >= 0) {
    perror("Agnocast is already open");
    exit(EXIT_FAILURE);
  }

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

  if (const char * env_p = std::getenv("INITIAL_MEMPOOL_SIZE")) {
    INITIAL_MEMPOOL_SIZE = std::stoull(std::string(env_p));
  }

  return map_area(pid, new_shm_args.ret_addr, true);
}

size_t read_mq_msgmax()
{
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

static void shutdown_agnocast()
{
  std::cout << "[Info]: shutdown_agnocast started" << std::endl;
  is_running = false;
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
      perror("close shm_fd failed");
    }
  }

  const std::string shm_name = "/agnocast@" + std::to_string(pid);
  if (shm_unlink(shm_name.c_str()) == -1) {
    perror("shm_unlink failed");
  }

  if (mq_close(mq_new_publisher) == -1) {
    perror("mq_close failed");
  }

  const std::string mq_name = "/new_publisher@" + std::to_string(pid);
  if (mq_unlink(mq_name.c_str()) == -1) {
    perror("mq_unlink failed");
  }

  for (auto & th : threads) {
    th.join();
  }

  std::cout << "[Info]: shutdown_agnocast completed" << std::endl;
}

class Cleanup
{
public:
  ~Cleanup() { shutdown_agnocast(); }
};

static Cleanup cleanup;

}  // namespace agnocast

#include "agnocast.hpp"

#include "agnocast_ioctl.hpp"
#include "agnocast_mq.hpp"

#include <atomic>
#include <cstdint>
#include <mutex>
#include <set>

namespace agnocast
{

int agnocast_fd = -1;
std::atomic<bool> is_running = true;
std::vector<std::thread> threads;
extern mqd_t mq_new_publisher;

std::vector<int> shm_fds;
std::mutex shm_fds_mtx;

bool ok()
{
  return is_running.load();
}

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
  const std::string shm_name = create_shm_name(pid);

  int oflag = writable ? O_CREAT | O_RDWR : O_RDONLY;
  const int shm_mode = 0666;
  int shm_fd = shm_open(shm_name.c_str(), oflag, shm_mode);
  if (shm_fd == -1) {
    RCLCPP_ERROR(logger, "shm_open failed: %s", strerror(errno));
    close(agnocast_fd);
    return nullptr;
  }

  {
    std::lock_guard<std::mutex> lock(shm_fds_mtx);
    shm_fds.push_back(shm_fd);
  }

  if (writable) {
    if (ftruncate(shm_fd, static_cast<off_t>(shm_size)) == -1) {
      RCLCPP_ERROR(logger, "ftruncate failed: %s", strerror(errno));
      close(agnocast_fd);
      return nullptr;
    }
  }

  int prot = writable ? PROT_READ | PROT_WRITE : PROT_READ;
  void * ret = mmap(
    reinterpret_cast<void *>(shm_addr), shm_size, prot, MAP_SHARED | MAP_FIXED_NOREPLACE, shm_fd,
    0);

  if (ret == MAP_FAILED) {
    RCLCPP_ERROR(logger, "mmap failed: %s", strerror(errno));
    close(agnocast_fd);
    return nullptr;
  }

  return ret;
}

void * map_writable_area(const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size)
{
  if (already_mapped(pid)) {
    RCLCPP_ERROR(logger, "map_writeable_area failed");
    close(agnocast_fd);
    return nullptr;
  }

  return map_area(pid, shm_addr, shm_size, true);
}

void map_read_only_area(const uint32_t pid, const uint64_t shm_addr, const uint64_t shm_size)
{
  if (already_mapped(pid)) {
    return;
  }
  if (map_area(pid, shm_addr, shm_size, false) == nullptr) {
    exit(EXIT_FAILURE);
  }
}

// NOTE: Avoid heap allocation inside initialize_agnocast. TLSF is not initialized yet.
void * initialize_agnocast(const uint64_t shm_size)
{
  if (agnocast_fd >= 0) {
    RCLCPP_ERROR(logger, "Agnocast is already open");
    return nullptr;
  }

  agnocast_fd = open("/dev/agnocast", O_RDWR);
  if (agnocast_fd < 0) {
    RCLCPP_ERROR(logger, "Failed to open the device: %s", strerror(errno));
    return nullptr;
  }

  const uint32_t pid = getpid();

  union ioctl_new_shm_args new_shm_args = {};
  new_shm_args.pid = pid;
  new_shm_args.shm_size = shm_size;
  if (ioctl(agnocast_fd, AGNOCAST_NEW_SHM_CMD, &new_shm_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_NEW_SHM_CMD failed");
    close(agnocast_fd);
    return nullptr;
  }
  return map_writable_area(pid, new_shm_args.ret_addr, shm_size);
}

static void shutdown_agnocast()
{
  printf("[INFO] [Agnocast]: shutdown_agnocast started\n");
  is_running.store(false);

  const uint32_t pid = getpid();

  {
    std::lock_guard<std::mutex> lock(shm_fds_mtx);
    for (int fd : shm_fds) {
      if (close(fd) == -1) {
        perror("[ERROR] [Agnocast] close shm_fd failed");
      }
    }
  }

  const std::string shm_name = create_shm_name(pid);
  if (shm_unlink(shm_name.c_str()) == -1) {
    perror("[ERROR] [Agnocast] shm_unlink failed");
  }

  if (mq_new_publisher != -1) {
    if (mq_close(mq_new_publisher) == -1) {
      perror("[ERROR] [Agnocast] mq_close failed");
    }

    const std::string mq_name = create_mq_name_new_publisher(pid);
    if (mq_unlink(mq_name.c_str()) == -1) {
      perror("[ERROR] [Agnocast] mq_unlink failed");
    }
  }

  for (auto & th : threads) {
    th.join();
  }

  printf("[INFO] [Agnocast]: shutdown_agnocast completed\n");
}

class Cleanup
{
public:
  Cleanup(const Cleanup &) = delete;
  Cleanup & operator=(const Cleanup &) = delete;
  Cleanup(Cleanup &&) = delete;
  Cleanup & operator=(Cleanup &&) = delete;

  Cleanup() = default;
  ~Cleanup() { shutdown_agnocast(); }
};

static Cleanup cleanup;

}  // namespace agnocast

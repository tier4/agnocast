#include "agnocast/agnocast.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_version.hpp"

#include <sys/types.h>

#include <atomic>
#include <cstdint>
#include <mutex>

namespace agnocast
{

int agnocast_fd = -1;
std::vector<int> shm_fds;
std::mutex shm_fds_mtx;

struct SemVer
{
  int major;
  int minor;
  int patch;

  static SemVer parse(const char * version)
  {
    SemVer result = {0, 0, 0};
    if (!version) return result;

    sscanf(version, "%d.%d.%d", &result.major, &result.minor, &result.patch);
    return result;
  }

  static bool is_compatible(const SemVer & v1, const SemVer & v2)
  {
    return (v1.major == v2.major && v1.minor == v2.minor);
  }
};

int check_version_consistency(
  const unsigned char * heaphook_version_ptr, const size_t heaphook_version_str_len,
  struct ioctl_get_version_args kmod_version)
{
  char heaphook_version[VERSION_BUFFER_LEN];
  size_t copy_len = heaphook_version_str_len < 32 ? heaphook_version_str_len : 32;
  heaphook_version[copy_len] = '\0';
  memcpy(heaphook_version, heaphook_version_ptr, copy_len);

  SemVer lib_version = SemVer::parse(agnocastlib::VERSION);
  SemVer heaphook_ver = SemVer::parse(heaphook_version);
  SemVer kmod_ver = SemVer::parse(kmod_version.version);

  if (!SemVer::is_compatible(lib_version, heaphook_ver)) {
    RCLCPP_INFO(
      logger, "Major.Minor versions must match: Agnocastlib(%d.%d) vs Agnocast heaphook(%d.%d)",
      lib_version.major, lib_version.minor, heaphook_ver.major, heaphook_ver.minor);
    return -1;
  }

  if (!SemVer::is_compatible(lib_version, kmod_ver)) {
    RCLCPP_INFO(
      logger,
      "Major.Minor versions must match: Agnocastlib(%d.%d) vs Agnocast kernel module(%d.%d)",
      lib_version.major, lib_version.minor, kmod_ver.major, kmod_ver.minor);
    return -1;
  }

  return 0;
}

void * map_area(
  const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size, const bool writable)
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

void * map_writable_area(const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size)
{
  return map_area(pid, shm_addr, shm_size, true);
}

void map_read_only_area(const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size)
{
  if (map_area(pid, shm_addr, shm_size, false) == nullptr) {
    exit(EXIT_FAILURE);
  }
}

// NOTE: Avoid heap allocation inside initialize_agnocast. TLSF is not initialized yet.
void * initialize_agnocast(
  const uint64_t shm_size, const unsigned char * heaphook_version_ptr,
  const size_t heaphook_version_str_len)
{
  if (agnocast_fd >= 0) {
    RCLCPP_ERROR(logger, "Agnocast is already open");
    exit(EXIT_FAILURE);
  }

  agnocast_fd = open("/dev/agnocast", O_RDWR);
  if (agnocast_fd < 0) {
    RCLCPP_ERROR(logger, "Failed to open the device: %s", strerror(errno));
    exit(EXIT_FAILURE);
  }

  struct ioctl_get_version_args get_version_args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_VERSION, &get_version_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_VERSION failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  if (
    check_version_consistency(heaphook_version_ptr, heaphook_version_str_len, get_version_args) <
    0) {
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  const pid_t pid = getpid();

  union ioctl_new_shm_args new_shm_args = {};
  new_shm_args.pid = pid;
  new_shm_args.shm_size = shm_size;
  if (ioctl(agnocast_fd, AGNOCAST_NEW_SHM_CMD, &new_shm_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_NEW_SHM_CMD failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return map_writable_area(pid, new_shm_args.ret_addr, shm_size);
}

static void shutdown_agnocast()
{
  std::lock_guard<std::mutex> lock(shm_fds_mtx);
  for (int fd : shm_fds) {
    if (close(fd) == -1) {
      perror("[ERROR] [Agnocast] close shm_fd failed");
    }
  }
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

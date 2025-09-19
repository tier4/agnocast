#include "agnocast/agnocast.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_version.hpp"

#include <sys/types.h>

#include <atomic>
#include <cstdint>
#include <mutex>

extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

int agnocast_fd = -1;
std::vector<int> shm_fds;
std::mutex shm_fds_mtx;
std::mutex mmap_mtx;
// mmap_mtx: Prevents a race condition and segfault between two threads
// in a multithreaded executor using the same mqueue_fd.
//
// Race Scenario:
// 1. Thread 1 (T1):
//    - Calls epoll_wait(), mq_receive(), then ioctl(RECEIVE_CMD), initially obtaining
//      publisher info (PID, shared memory address `shm_addr`).
//    - Critical: OS context switch occurs *after* ioctl() but *before* T1 fully
//      processes/maps `shm_addr`.
// 2. Thread 2 (T2):
//    - Calls epoll_wait(), mq_receive(), then ioctl(RECEIVE_CMD) on the same mqueue_fd,
//      but does *not* receive publisher info (assuming it's already set up).
//    - Proceeds to a callback which attempts to use `shm_addr`, leading to a SEGFAULT.
//
// Root Cause: T2's callback uses `shm_addr` that T1 fetched but hadn't initialized/mapped yet.
// This mutex ensures atomicity for T1's critical section: from ioctl fetching publisher
// info through to completing shared memory setup.

mqd_t open_bridge_receiver_queue()
{
  std::string mq_name = create_mq_name_for_bridge();
  struct mq_attr attr = {};
  attr.mq_maxmsg = 10;
  attr.mq_msgsize = sizeof(agnocast::MqMsgBridge);
  mqd_t mq = mq_open(mq_name.c_str(), O_RDONLY | O_CREAT, 0644, &attr);

  if (mq == (mqd_t)-1) {
    std::cerr << "mq_open failed for " << mq_name << ": " << strerror(errno) << std::endl;
    return (mqd_t)-1;
  }

  return mq;
}

static bool receive_message(mqd_t mq, agnocast::MqMsgBridge & msg_buffer)
{
  struct timespec ts;
  if (clock_gettime(CLOCK_REALTIME, &ts) == -1) {
    RCLCPP_ERROR(logger, "clock_gettime failed: %s", strerror(errno));
    sleep(1);
    return false;
  }
  ts.tv_sec += 1;

  ssize_t bytes_read =
    mq_timedreceive(mq, reinterpret_cast<char *>(&msg_buffer), sizeof(msg_buffer), NULL, &ts);

  if (bytes_read < 0) {
    if (errno != ETIMEDOUT) {
      RCLCPP_ERROR(logger, "mq_timedreceive failed: %s", strerror(errno));
    }
    return false;
  }

  if (static_cast<size_t>(bytes_read) != sizeof(agnocast::MqMsgBridge)) {
    RCLCPP_WARN(
      logger, "Received message with unexpected size: %zd vs %zu", bytes_read,
      sizeof(agnocast::MqMsgBridge));
    return false;
  }

  return true;
}

void start_bridge(agnocast::MqMsgBridge received_msg)
{
  if (setsid() == -1) {
    RCLCPP_ERROR(logger, "setsid failed for unlink daemon: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  std::cout << "[BG PROCESS] PID: " << getpid() << ". Ready ..." << std::endl;

  if (!agnocast_heaphook_init_daemon()) {
    std::cerr << "[BG PROCESS] (Daemon) Heaphook init FAILED." << std::endl;
  }

  bridge_process_main(received_msg);
}

static void fork_bridge_daemon(
  const agnocast::MqMsgBridge & msg_buffer, std::map<pid_t, std::string> & active_daemons)
{
  pid_t pid = fork();

  if (pid < 0) {
    RCLCPP_ERROR(logger, "fork failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  if (pid == 0) {
    start_bridge(msg_buffer);
    exit(EXIT_SUCCESS);
  }

  active_daemons[pid] = msg_buffer.args.topic_name;
}

static void monitor_active_daemons(std::map<pid_t, std::string> & active_daemons)
{
  for (auto it = active_daemons.begin(); it != active_daemons.end();) {
    pid_t pid = it->first;
    std::string topic_name_str = it->second;

    union ioctl_get_subscriber_num_args get_subscriber_count_args = {};
    get_subscriber_count_args.topic_name = {topic_name_str.c_str(), topic_name_str.size()};

    if (ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) < 0) {
      RCLCPP_ERROR(
        logger, "AGNOCAST_GET_SUBSCRIBER_NUM_CMD failed for topic '%s': %s", topic_name_str.c_str(),
        strerror(errno));
      ++it;
      continue;
    }

    if (get_subscriber_count_args.ret_subscriber_num == 0) {
      RCLCPP_INFO(
        logger, "No subscribers for topic '%s'. Sending SIGTERM to PID %d", topic_name_str.c_str(),
        pid);
      if (kill(pid, SIGTERM) == -1) {
        if (errno != ESRCH) {
          RCLCPP_ERROR(logger, "Failed to send SIGTERM to PID %d: %s", pid, strerror(errno));
        }
      }
      it = active_daemons.erase(it);
    } else {
      ++it;
    }
  }
}

void poll_for_unlink()
{
  if (setsid() == -1) {
    RCLCPP_ERROR(logger, "setsid failed for unlink daemon: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  std::cout << "[POLL PROCESS] PID: " << getpid() << ". Ready ..." << std::endl;

  mqd_t mq = open_bridge_receiver_queue();
  if (mq == (mqd_t)-1) {
    exit(EXIT_FAILURE);
  }

  std::map<pid_t, std::string> active_daemons;
  agnocast::MqMsgBridge msg_buffer;

  while (true) {
    if (receive_message(mq, msg_buffer)) {
      fork_bridge_daemon(msg_buffer, active_daemons);
    }

    monitor_active_daemons(active_daemons);

    struct ioctl_get_exit_process_args get_exit_process_args = {};
    do {
      get_exit_process_args = {};
      if (ioctl(agnocast_fd, AGNOCAST_GET_EXIT_PROCESS_CMD, &get_exit_process_args) < 0) {
        RCLCPP_ERROR(logger, "AGNOCAST_GET_EXIT_PROCESS_CMD failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      if (get_exit_process_args.ret_pid > 0) {
        const std::string shm_name = create_shm_name(get_exit_process_args.ret_pid);
        shm_unlink(shm_name.c_str());

        if (active_daemons.count(get_exit_process_args.ret_pid)) {
          active_daemons.erase(get_exit_process_args.ret_pid);
        }
      }
    } while (get_exit_process_args.ret_pid > 0);

    if (get_exit_process_args.ret_daemon_should_exit) {
      break;
    }
  }

  mq_close(mq);
  exit(0);
}

struct semver
{
  int major;
  int minor;
  int patch;
};

bool parse_semver(const char * version, struct semver * out_ver)
{
  if (version == nullptr || out_ver == nullptr) {
    return false;
  }

  out_ver->major = 0;
  out_ver->minor = 0;
  out_ver->patch = 0;

  std::string version_str(version);
  std::stringstream ss(version_str);

  int64_t major = 0;
  int64_t minor = 0;
  int64_t patch = 0;

  if (!(ss >> major) || ss.get() != '.') {
    return false;
  }

  if (!(ss >> minor) || ss.get() != '.') {
    return false;
  }

  if (!(ss >> patch)) {
    return false;
  }

  if (!ss.eof()) {
    char remaining = '\0';
    if (ss >> remaining) {
      return false;
    }
  }

  if (major < 0 || minor < 0 || patch < 0) {
    return false;
  }

  out_ver->major = static_cast<int>(major);
  out_ver->minor = static_cast<int>(minor);
  out_ver->patch = static_cast<int>(patch);

  return true;
}

bool compare_to_minor_version(const struct semver * v1, const struct semver * v2)
{
  if (v1 == nullptr || v2 == nullptr) {
    return false;
  }

  return (v1->major == v2->major && v1->minor == v2->minor);
}

bool compare_to_patch_version(const struct semver * v1, const struct semver * v2)
{
  if (v1 == nullptr || v2 == nullptr) {
    return false;
  }

  return (v1->major == v2->major && v1->minor == v2->minor && v1->patch == v2->patch);
}

bool is_version_consistent(
  const unsigned char * heaphook_version_ptr, const size_t heaphook_version_str_len,
  struct ioctl_get_version_args kmod_version)
{
  std::array<char, VERSION_BUFFER_LEN> heaphook_version_arr{};
  struct semver lib_ver{};
  struct semver heaphook_ver{};
  struct semver kmod_ver{};

  size_t copy_len = heaphook_version_str_len < (VERSION_BUFFER_LEN - 1) ? heaphook_version_str_len
                                                                        : (VERSION_BUFFER_LEN - 1);
  std::memcpy(heaphook_version_arr.data(), heaphook_version_ptr, copy_len);
  heaphook_version_arr[copy_len] = '\0';

  bool parse_lib_result = parse_semver(agnocastlib::VERSION, &lib_ver);
  bool parse_heaphook_result = parse_semver(heaphook_version_arr.data(), &heaphook_ver);
  bool parse_kmod_result =
    parse_semver(static_cast<const char *>(&kmod_version.ret_version[0]), &kmod_ver);

  if (!parse_lib_result || !parse_heaphook_result || !parse_kmod_result) {
    RCLCPP_ERROR(logger, "Failed to parse one or more version strings");
    return false;
  }

  if (!compare_to_patch_version(&lib_ver, &heaphook_ver)) {
    RCLCPP_ERROR(
      logger,
      "Agnocast Heaphook and Agnocastlib versions must match exactly: Major, Minor, and Patch "
      "versions must all be identical. (agnocast-heaphook(%d.%d.%d), agnocast(%d.%d.%d))",
      heaphook_ver.major, heaphook_ver.minor, heaphook_ver.patch, lib_ver.major, lib_ver.minor,
      lib_ver.patch);
    return false;
  }

  if (!compare_to_minor_version(&lib_ver, &kmod_ver)) {
    RCLCPP_ERROR(
      logger,
      "Agnocast Kernel Module and Agnocastlib must be compatible: Major and Minor versions must "
      "match. (agnocast-kmod(%d.%d.%d), agnocast(%d.%d.%d))",
      kmod_ver.major, kmod_ver.minor, kmod_ver.patch, lib_ver.major, lib_ver.minor, lib_ver.patch);
    return false;
  }

  return true;
}

void * map_area(
  const pid_t pid, const uint64_t shm_addr, const uint64_t shm_size, const bool writable)
{
  const std::string shm_name = create_shm_name(pid);

  int oflag = writable ? O_CREAT | O_EXCL | O_RDWR : O_RDONLY;
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

    const int new_shm_mode = 0444;
    if (fchmod(shm_fd, new_shm_mode) == -1) {
      RCLCPP_ERROR(logger, "fchmod failed: %s", strerror(errno));
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
  if (ioctl(agnocast_fd, AGNOCAST_GET_VERSION_CMD, &get_version_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_VERSION_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  if (!is_version_consistent(heaphook_version_ptr, heaphook_version_str_len, get_version_args)) {
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  union ioctl_add_process_args add_process_args = {};
  add_process_args.shm_size = shm_size;
  if (ioctl(agnocast_fd, AGNOCAST_ADD_PROCESS_CMD, &add_process_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_ADD_PROCESS_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // Create a shm_unlink daemon process if it doesn't exist in its ipc namespace.
  if (!add_process_args.ret_unlink_daemon_exist) {
    pid_t pid = fork();

    if (pid < 0) {
      RCLCPP_ERROR(logger, "fork failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (pid == 0) {
      poll_for_unlink();
    }
  }

  void * mempool_ptr = map_writable_area(getpid(), add_process_args.ret_addr, shm_size);
  if (mempool_ptr == nullptr) {
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  return mempool_ptr;
}

extern "C" void * agnocast_child_initialize_pool(const uint64_t shm_size)
{
  union ioctl_add_process_args add_process_args = {};
  add_process_args.shm_size = shm_size;
  if (ioctl(agnocast_fd, AGNOCAST_ADD_PROCESS_CMD, &add_process_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_ADD_PROCESS_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  void * mempool_ptr = map_writable_area(getpid(), add_process_args.ret_addr, shm_size);
  if (mempool_ptr == nullptr) {
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
  return mempool_ptr;
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

#include "agnocast/agnocast.hpp"

#include "agnocast/agnocast_bridge_plugin_api.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_version.hpp"

#include <ament_index_cpp/get_package_prefix.hpp>

#include <dlfcn.h>
#include <sys/types.h>

#include <atomic>
#include <cstdint>
#include <fstream>
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

struct ActiveBridgeR2A
{
  std::string topic_name;
  rclcpp::SubscriptionBase::SharedPtr subscription;
  void * plugin_handle;
};

struct ActiveBridgeA2R
{
  std::string topic_name;
  std::shared_ptr<agnocast::SubscriptionBase> subscription;
  void * plugin_handle;
};

void launch_r2a_bridge_thread(
  rclcpp::Node::SharedPtr node, const BridgeRequest request,
  std::vector<ActiveBridgeR2A> & active_bridges, std::mutex & mutex)
{
  auto logger = node->get_logger();
  std::string r2a_plugin_path;
  try {
    const std::string package_prefix = ament_index_cpp::get_package_prefix("agnocastlib");

    std::string type_name = request.message_type;
    std::replace(type_name.begin(), type_name.end(), '/', '_');

    r2a_plugin_path =
      package_prefix + "/lib/agnocastlib/bridge_plugins/libr2a_bridge_plugin_" + type_name + ".so";

  } catch (const ament_index_cpp::PackageNotFoundError & e) {
    RCLCPP_ERROR(
      logger, "Could not find package 'agnocastlib' to locate plugins. Error: %s", e.what());
    return;
  }

  void * r2a_handle = dlopen(r2a_plugin_path.c_str(), RTLD_LAZY);
  if (!r2a_handle) {
    RCLCPP_ERROR(
      logger, "[BRIDGE THREAD] Failed to load plugin '%s'. Error: %s", r2a_plugin_path.c_str(),
      dlerror());
    return;
  }

  CreateR2ABridgeFunc create_r2a_bridge_ptr =
    reinterpret_cast<CreateR2ABridgeFunc>(dlsym(r2a_handle, "create_r2a_bridge"));

  const char * dlsym_error = dlerror();
  if (dlsym_error != nullptr) {
    RCLCPP_ERROR(
      logger, "[BRIDGE THREAD] Failed to find symbol 'create_r2a_bridge' in '%s'. Error: %s",
      r2a_plugin_path.c_str(), dlsym_error);
    dlclose(r2a_handle);
    return;
  }
  auto subscription = create_r2a_bridge_ptr(node, std::string(request.topic_name), rclcpp::QoS(10));

  if (subscription) {
    std::lock_guard<std::mutex> lock(mutex);
    active_bridges.push_back({request.topic_name, subscription, r2a_handle});
    RCLCPP_INFO(
      logger, "[BRIDGE THREAD] R2A Bridge for topic '%s' created and is now active.",
      request.topic_name);
  } else {
    RCLCPP_ERROR(
      logger,
      "[BRIDGE THREAD] create_r2a_bridge function returned a null subscription for topic '%s'.",
      request.topic_name);
    dlclose(r2a_handle);
  }
}

void launch_a2r_bridge_thread(
  rclcpp::Node::SharedPtr node, const BridgeRequest request,
  std::vector<ActiveBridgeA2R> & active_bridges, std::mutex & mutex)
{
  auto logger = node->get_logger();
  std::string a2r_plugin_path;
  try {
    const std::string package_prefix = ament_index_cpp::get_package_prefix("agnocastlib");

    std::string type_name = request.message_type;
    std::replace(type_name.begin(), type_name.end(), '/', '_');

    a2r_plugin_path =
      package_prefix + "/lib/agnocastlib/bridge_plugins/liba2r_bridge_plugin_" + type_name + ".so";

  } catch (const ament_index_cpp::PackageNotFoundError & e) {
    RCLCPP_ERROR(
      logger, "Could not find package 'agnocastlib' to locate plugins. Error: %s", e.what());
    return;
  }

  void * a2r_handle = dlopen(a2r_plugin_path.c_str(), RTLD_LAZY);
  if (!a2r_handle) {
    RCLCPP_ERROR(
      logger, "[BRIDGE THREAD] Failed to load plugin '%s'. Error: %s", a2r_plugin_path.c_str(),
      dlerror());
    return;
  }

  CreateA2RBridgeFunc create_a2r_bridge_ptr =
    reinterpret_cast<CreateA2RBridgeFunc>(dlsym(a2r_handle, "create_a2r_bridge"));

  const char * dlsym_error = dlerror();
  if (dlsym_error != nullptr) {
    RCLCPP_ERROR(
      logger, "[BRIDGE THREAD] Failed to find symbol 'create_a2r_bridge' in '%s'. Error: %s",
      a2r_plugin_path.c_str(), dlsym_error);
    dlclose(a2r_handle);
    return;
  }
  auto subscription = create_a2r_bridge_ptr(node, std::string(request.topic_name), rclcpp::QoS(10));

  if (subscription) {
    std::lock_guard<std::mutex> lock(mutex);
    active_bridges.push_back({request.topic_name, subscription, a2r_handle});
    RCLCPP_INFO(
      logger, "[BRIDGE THREAD] A2R Bridge for topic '%s' created and is now active.",
      request.topic_name);
  } else {
    RCLCPP_ERROR(
      logger,
      "[BRIDGE THREAD] create_a2r_bridge function returned a null subscription for topic '%s'.",
      request.topic_name);
    dlclose(a2r_handle);
  }
}

void load_filter_file(std::unordered_set<std::string> & allowed_topics, rclcpp::Logger logger)
{
  const char * filter_file_path = getenv("AGNOCAST_BRIDGE_FILTER_FILE");

  if (filter_file_path) {
    RCLCPP_INFO(logger, "[BRIDGE MANAGER DAEMON] Loading topic filter from: %s", filter_file_path);
    std::ifstream filter_file(filter_file_path);
    if (filter_file.is_open()) {
      std::string topic_name;
      while (std::getline(filter_file, topic_name)) {
        if (!topic_name.empty() && topic_name[0] != '#') {
          allowed_topics.insert(topic_name);
        }
      }
      RCLCPP_INFO(
        logger, "[BRIDGE MANAGER DAEMON] Loaded %zu topics into the filter.",
        allowed_topics.size());
    } else {
      RCLCPP_WARN(
        logger,
        "[BRIDGE MANAGER DAEMON] Could not open filter file: %s. All topics will be allowed.",
        filter_file_path);
    }
  } else {
    RCLCPP_INFO(
      logger, "[BRIDGE MANAGER DAEMON] No filter file specified. All topics will be allowed.");
  }
}

std::unique_ptr<rclcpp::Executor> select_executor(rclcpp::Logger logger)
{
  std::unique_ptr<rclcpp::Executor> executor;
  const char * executor_type_env = getenv("AGNOCAST_EXECUTOR_TYPE");
  std::string executor_type = executor_type_env ? executor_type_env : "single";

  if (executor_type == "multi") {
    RCLCPP_INFO(logger, "[BRIDGE MANAGER DAEMON] Using MultiThreadedAgnocastExecutor.");
    // std::make_unique<...>(4))
    executor = std::make_unique<agnocast::MultiThreadedAgnocastExecutor>();
  } else if (executor_type == "isolated") {
    RCLCPP_INFO(logger, "[BRIDGE MANAGER DAEMON] Using CallbackIsolatedAgnocastExecutor.");
    executor = std::make_unique<agnocast::CallbackIsolatedAgnocastExecutor>();
  } else {
    RCLCPP_INFO(logger, "[BRIDGE MANAGER DAEMON] Using SingleThreadedAgnocastExecutor (default).");
    executor = std::make_unique<agnocast::SingleThreadedAgnocastExecutor>();
  }

  return executor;
}

void handle_bridge_request(
  mqd_t mq, rclcpp::Node::SharedPtr node, std::unordered_set<std::string> & allowed_topics,
  std::vector<ActiveBridgeR2A> & active_r2a_bridges,
  std::vector<ActiveBridgeA2R> & active_a2r_bridges, std::vector<std::thread> & worker_threads,
  std::mutex & bridge_mutex)
{
  BridgeRequest req;
  if (mq_receive(mq, (char *)&req, sizeof(BridgeRequest), NULL) >= 0) {
    if (
      !allowed_topics.empty() &&
      allowed_topics.find(std::string(req.topic_name)) == allowed_topics.end()) {
      RCLCPP_INFO(
        logger, "Bridge request for Topic='%s' was ignored due to filter rules.", req.topic_name);
      return;
    }

    std::lock_guard<std::mutex> lock(bridge_mutex);
    bool already_exists = false;

    for (const auto & bridge : active_r2a_bridges) {
      if (
        bridge.topic_name == std::string(req.topic_name) &&
        req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
        already_exists = true;
        break;
      }
    }

    for (const auto & bridge : active_a2r_bridges) {
      if (
        bridge.topic_name == std::string(req.topic_name) &&
        req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
        already_exists = true;
        break;
      }
    }

    if (already_exists) {
      return;
    }

    if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
      worker_threads.emplace_back(
        launch_r2a_bridge_thread, node, req, std::ref(active_r2a_bridges), std::ref(bridge_mutex));
    } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
      worker_threads.emplace_back(
        launch_a2r_bridge_thread, node, req, std::ref(active_a2r_bridges), std::ref(bridge_mutex));
    }
  }
}

void shutdown_manager(
  std::thread & spin_thread, std::vector<std::thread> & worker_threads,
  std::vector<ActiveBridgeR2A> & active_r2a_bridges,
  std::vector<ActiveBridgeA2R> & active_a2r_bridges, mqd_t mq, const std::string & mq_name)
{
  rclcpp::shutdown();

  if (spin_thread.joinable()) {
    spin_thread.join();
  }

  for (auto & th : worker_threads) {
    if (th.joinable()) {
      th.join();
    }
  }

  for (auto & bridge : active_r2a_bridges) {
    dlclose(bridge.plugin_handle);
  }
  active_r2a_bridges.clear();

  for (auto & bridge : active_a2r_bridges) {
    dlclose(bridge.plugin_handle);
  }
  active_a2r_bridges.clear();

  mq_close(mq);
  mq_unlink(mq_name.c_str());
}

void check_and_shutdown_idle_bridges(
  rclcpp::Logger logger, std::vector<ActiveBridgeR2A> & r2a_bridges,
  std::vector<ActiveBridgeA2R> & a2r_bridges, std::mutex & mutex)
{
  std::lock_guard<std::mutex> lock(mutex);
  const pid_t self_pid = getpid();

  r2a_bridges.erase(
    std::remove_if(
      r2a_bridges.begin(), r2a_bridges.end(),
      [&](const ActiveBridgeR2A & bridge) {
        union ioctl_get_ext_subscriber_num_args args = {};
        args.topic_name = {bridge.topic_name.c_str(), bridge.topic_name.size()};
        args.exclude_pid = self_pid;

        if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_SUBSCRIBER_NUM_CMD, &args) < 0) {
          RCLCPP_WARN(
            logger, "Failed to get external subscriber count for '%s'", bridge.topic_name.c_str());
          return false;
        }

        if (args.ret_ext_subscriber_num == 0) {
          dlclose(bridge.plugin_handle);
          return true;
        }
        return false;
      }),
    r2a_bridges.end());

  a2r_bridges.erase(
    std::remove_if(
      a2r_bridges.begin(), a2r_bridges.end(),
      [&](const ActiveBridgeA2R & bridge) {
        union ioctl_get_ext_publisher_num_args args = {};
        args.topic_name = {bridge.topic_name.c_str(), bridge.topic_name.size()};
        args.exclude_pid = self_pid;

        if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_PUBLISHER_NUM_CMD, &args) < 0) {
          RCLCPP_WARN(
            logger, "Failed to get external publisher count for '%s'", bridge.topic_name.c_str());
          return false;
        }

        if (args.ret_ext_publisher_num == 0) {
          dlclose(bridge.plugin_handle);
          return true;
        }
        return false;
      }),
    a2r_bridges.end());
}

void check_and_shutdown_daemon_if_idle(
  rclcpp::Logger logger, std::vector<ActiveBridgeR2A> & r2a_bridges,
  std::vector<ActiveBridgeA2R> & a2r_bridges, std::mutex & mutex)
{
  {
    std::lock_guard<std::mutex> lock(mutex);
    if (!r2a_bridges.empty() || !a2r_bridges.empty()) {
      return;
    }
  }

  struct ioctl_get_active_process_num_args args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_ACTIVE_PROCESS_NUM_CMD, &args) < 0) {
    RCLCPP_WARN(logger, "Failed to get active process count from kernel module.");
    return;
  }

  if (args.ret_active_process_num <= 1) {
    rclcpp::shutdown();
  }
}

void bridge_manager_daemon()
{
  if (setsid() == -1) {
    RCLCPP_ERROR(logger, "setsid failed for bridge manager daemon: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  signal(SIGINT, SIG_IGN);

  std::vector<std::thread> worker_threads;
  std::vector<ActiveBridgeR2A> active_r2a_bridges;
  std::vector<ActiveBridgeA2R> active_a2r_bridges;
  std::mutex bridge_mutex;

  rclcpp::init(0, nullptr);
  auto node = std::make_shared<rclcpp::Node>("agnocast_bridge_manager");
  auto logger = node->get_logger();

  if (!agnocast_heaphook_init_daemon()) {
    RCLCPP_ERROR(logger, "Heaphook init FAILED.");
  }

  const std::string mq_name_str = create_mq_name_for_bridge();
  const char * mq_name = mq_name_str.c_str();
  struct mq_attr attr;
  attr.mq_flags = 0;
  attr.mq_maxmsg = 10;
  attr.mq_msgsize = sizeof(BridgeRequest);
  attr.mq_curmsgs = 0;
  mq_unlink(mq_name);
  mqd_t mq = mq_open(mq_name, O_CREAT | O_RDONLY, 0644, &attr);
  if (mq == (mqd_t)-1) {
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  RCLCPP_INFO(logger, "[BRIDGE MANAGER DAEMON] PID: %d", getpid());

  std::unordered_set<std::string> allowed_topics;
  load_filter_file(allowed_topics, logger);
  auto executor = select_executor(logger);

  executor->add_node(node);
  std::thread spin_thread([&]() {
    RCLCPP_INFO(logger, "[BRIDGE MANAGER DAEMON] Starting AgnoCast Executor spin thread.");
    executor->spin();
  });

  while (rclcpp::ok()) {
    fd_set fds;
    FD_ZERO(&fds);
    FD_SET(mq, &fds);

    int max_fd = static_cast<int>(mq) + 1;

    struct timeval timeout;
    timeout.tv_sec = 1;
    timeout.tv_usec = 0;

    int ret = select(max_fd, &fds, NULL, NULL, &timeout);

    if (ret < 0) {
      if (errno == EINTR) continue;
      RCLCPP_ERROR(logger, "select() failed: %s", strerror(errno));
      break;
    }

    if (ret == 0) {
      check_and_shutdown_idle_bridges(logger, active_r2a_bridges, active_a2r_bridges, bridge_mutex);
      check_and_shutdown_daemon_if_idle(
        logger, active_r2a_bridges, active_a2r_bridges, bridge_mutex);
      continue;
    }

    if (FD_ISSET(mq, &fds)) {
      handle_bridge_request(
        mq, node, allowed_topics, active_r2a_bridges, active_a2r_bridges, worker_threads,
        bridge_mutex);
      check_and_shutdown_idle_bridges(logger, active_r2a_bridges, active_a2r_bridges, bridge_mutex);
    }
  }

  shutdown_manager(
    spin_thread, worker_threads, active_r2a_bridges, active_a2r_bridges, mq, mq_name_str);
  exit(0);
}

void poll_for_unlink()
{
  if (setsid() == -1) {
    RCLCPP_ERROR(logger, "setsid failed for unlink daemon: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  RCLCPP_INFO(logger, "[POLL FOR UNLINK] PID: %d", getpid());

  while (true) {
    sleep(1);

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
      }
    } while (get_exit_process_args.ret_pid > 0);

    if (get_exit_process_args.ret_daemon_should_exit) {
      break;
    }
  }

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

  agnocast_fd = open("/dev/agnocast", O_RDWR | O_CLOEXEC);
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

    pid_t pid2 = fork();

    if (pid2 < 0) {
      RCLCPP_ERROR(logger, "fork failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (pid2 == 0) {
      bridge_manager_daemon();
    }
  }

  const std::string mq_name_str = create_mq_name_for_bridge();
  constexpr int max_retries = 10;
  constexpr auto retry_delay = std::chrono::milliseconds(100);
  bool mq_ready = false;

  for (int i = 0; i < max_retries; ++i) {
    mqd_t mq_test = mq_open(mq_name_str.c_str(), O_WRONLY);
    if (mq_test != (mqd_t)-1) {
      mq_close(mq_test);
      mq_ready = true;
      break;
    }
    std::this_thread::sleep_for(retry_delay);
  }

  if (!mq_ready) {
    RCLCPP_ERROR(logger, "Failed to connect to bridge manager message queue after timeout.");
    exit(EXIT_FAILURE);
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

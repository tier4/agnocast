#include "agnocast/agnocast_bridge_generator.hpp"

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <link.h>
#include <mqueue.h>
#include <sys/prctl.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstring>
#include <iostream>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <thread>
#include <vector>

extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

BridgeGenerator::BridgeGenerator(pid_t target_pid)
: target_pid_(target_pid), logger_(rclcpp::get_logger("agnocast_bridge_generator"))
{
  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  rclcpp::InitOptions init_options;
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  if (!agnocast_heaphook_init_daemon()) {
    throw std::runtime_error("Failed to initialize Agnocast HeapHook Daemon.");
  }

  setup_mq();
  setup_signals();
  setup_epoll();
}

BridgeGenerator::~BridgeGenerator()
{
  RCLCPP_INFO(logger_, "Agnocast Bridge Generator shutting down.");

  if (executor_) {
    executor_->cancel();
  }
  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  if (epoll_fd_ != -1) close(epoll_fd_);
  if (signal_fd_ != -1) close(signal_fd_);

  if (mq_parent_fd_ != (mqd_t)-1) mq_close(mq_parent_fd_);
  if (!mq_parent_name_.empty()) mq_unlink(mq_parent_name_.c_str());

  if (mq_child_fd_ != (mqd_t)-1) mq_close(mq_child_fd_);
  if (!mq_child_name_.empty()) mq_unlink(mq_child_name_.c_str());

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void BridgeGenerator::run()
{
  std::string proc_name = "agno_br_" + std::to_string(getpid());
  if (prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0) != 0) {
    RCLCPP_WARN(logger_, "Failed to set process name: %s", strerror(errno));
  }

  setup_ros_execution();

  constexpr int MAX_EVENTS = 10;
  struct epoll_event events[MAX_EVENTS];

  auto last_gc_time = std::chrono::steady_clock::now();
  constexpr auto GC_INTERVAL = std::chrono::seconds(1);

  while (!shutdown_requested_ && rclcpp::ok()) {
    check_parent_alive();

    auto now = std::chrono::steady_clock::now();
    if (now - last_gc_time >= GC_INTERVAL) {
      check_connection_demand();
      last_gc_time = now;
      std::lock_guard<std::mutex> lock(executor_mutex_);
      check_should_exit();
    }

    if (shutdown_requested_) break;

    int n = epoll_wait(epoll_fd_, events, MAX_EVENTS, 1000);
    if (n < 0) {
      if (errno == EINTR) continue;
      break;
    }

    handle_epoll_events(events, n);
  }
}

void BridgeGenerator::setup_mq()
{
  auto create_and_open = [](const std::string & name) -> mqd_t {
    struct mq_attr attr{};
    attr.mq_maxmsg = 10;
    attr.mq_msgsize = sizeof(MqMsgBridge);
    mq_unlink(name.c_str());

    mqd_t fd = mq_open(name.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK | O_CLOEXEC, 0600, &attr);

    if (fd == (mqd_t)-1) {
      throw std::runtime_error("mq_open failed for " + name + ": " + std::string(strerror(errno)));
    }
    return fd;
  };

  mq_parent_name_ = create_mq_name_for_bridge_parent(target_pid_);
  mq_parent_fd_ = create_and_open(mq_parent_name_);

  mq_child_name_ = create_mq_name_for_bridge_child(getpid());
  mq_child_fd_ = create_and_open(mq_child_name_);
}

void BridgeGenerator::setup_signals()
{
  for (int sig : {SIGPIPE, SIGHUP}) {
    ::signal(sig, SIG_IGN);
  }

  sigset_t mask;
  sigemptyset(&mask);
  for (int sig : {SIGTERM, SIGINT}) {
    sigaddset(&mask, sig);
  }

  if (sigprocmask(SIG_BLOCK, &mask, nullptr) == -1) {
    throw std::runtime_error("sigprocmask failed: " + std::string(strerror(errno)));
  }

  signal_fd_ = signalfd(-1, &mask, SFD_NONBLOCK | SFD_CLOEXEC);
  if (signal_fd_ == -1) {
    throw std::runtime_error("signalfd failed: " + std::string(strerror(errno)));
  }
}

void BridgeGenerator::setup_epoll()
{
  epoll_fd_ = epoll_create1(EPOLL_CLOEXEC);
  if (epoll_fd_ == -1) {
    throw std::runtime_error("epoll_create1 failed: " + std::string(strerror(errno)));
  }

  auto add_to_epoll = [this](int fd, const std::string & label) {
    struct epoll_event ev{};
    ev.events = EPOLLIN;
    ev.data.fd = fd;

    if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, fd, &ev) == -1) {
      throw std::runtime_error("epoll_ctl (" + label + ") failed: " + std::string(strerror(errno)));
    }
  };

  add_to_epoll(mq_parent_fd_, "Parent MQ");
  add_to_epoll(mq_child_fd_, "Child MQ");
  add_to_epoll(signal_fd_, "Signal");
}

void BridgeGenerator::setup_ros_execution()
{
  std::string node_name = "agnocast_bridge_node_" + std::to_string(getpid());
  container_node_ = std::make_shared<rclcpp::Node>(node_name);

  executor_ =
    std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(rclcpp::ExecutorOptions(), 0, 0);

  executor_->add_node(container_node_);

  executor_thread_ = std::thread([this]() {
    try {
      this->executor_->spin();
    } catch (const std::exception & e) {
      RCLCPP_FATAL(logger_, "Executor Thread CRASHED: %s", e.what());
    } catch (...) {
      RCLCPP_FATAL(logger_, "Executor Thread CRASHED (Unknown)");
    }
  });
}

void BridgeGenerator::handle_epoll_events(const struct epoll_event * events, int count)
{
  for (int i = 0; i < count; ++i) {
    int fd = events[i].data.fd;

    if (fd == mq_parent_fd_) {
      handle_mq_event(mq_parent_fd_, true);
    } else if (fd == mq_child_fd_) {
      handle_mq_event(mq_child_fd_, false);
    } else if (fd == signal_fd_) {
      handle_signal_event();
    }
  }
}

void BridgeGenerator::handle_mq_event(mqd_t fd, bool allow_delegation)
{
  MqMsgBridge req;
  while (mq_receive(fd, (char *)&req, sizeof(req), nullptr) > 0) {
    std::string unique_key = req.target.topic_name;
    unique_key += (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_R2A" : "_A2R";

    std::lock_guard<std::mutex> lock(executor_mutex_);

    if (active_bridges_.count(unique_key)) {
      RCLCPP_INFO(logger_, "Request for '%s': Already active.", unique_key.c_str());
      continue;
    }

    struct ioctl_bridge_args args;
    std::memset(&args, 0, sizeof(args));
    args.pid = getpid();
    snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", req.target.topic_name);

    if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &args) == 0) {
      RCLCPP_INFO(logger_, "Registered/Confirmed owner for '%s'. Creating...", unique_key.c_str());
      create_bridge_safely(req, unique_key);
      continue;
    }

    if (errno != EEXIST) {
      RCLCPP_ERROR(logger_, "Register bridge failed: %s", strerror(errno));
      continue;
    }

    if (!allow_delegation) {
      RCLCPP_WARN(
        logger_, "Delegate request failed (EEXIST). Another process took ownership of '%s'. Stop.",
        args.topic_name);
      continue;
    }

    union ioctl_get_bridge_pid_args pid_args;
    std::memset(&pid_args, 0, sizeof(pid_args));
    snprintf(pid_args.topic_name, MAX_TOPIC_NAME_LEN, "%s", req.target.topic_name);

    if (ioctl(agnocast_fd, AGNOCAST_GET_BRIDGE_PID_CMD, &pid_args) == 0) {
      pid_t owner_pid = pid_args.ret_pid;
      send_delegate_request(owner_pid, req);
      RCLCPP_INFO(logger_, "Delegated '%s' to PID %d", unique_key.c_str(), owner_pid);
    } else {
      RCLCPP_ERROR(logger_, "Race condition: Owner not found for '%s'", args.topic_name);
    }
  }
}

void BridgeGenerator::handle_signal_event()
{
  struct signalfd_siginfo fdsi;
  ssize_t s = read(signal_fd_, &fdsi, sizeof(struct signalfd_siginfo));

  if (s != sizeof(struct signalfd_siginfo)) {
    return;
  }

  if (fdsi.ssi_signo != SIGTERM && fdsi.ssi_signo != SIGINT) {
    return;
  }

  shutdown_requested_ = true;
  if (executor_) {
    executor_->cancel();
  }
}

void BridgeGenerator::check_parent_alive()
{
  if (!is_parent_alive_) return;

  if (kill(target_pid_, 0) != 0) {
    is_parent_alive_ = false;

    if (mq_parent_fd_ != (mqd_t)-1) {
      epoll_ctl(epoll_fd_, EPOLL_CTL_DEL, mq_parent_fd_, nullptr);
      mq_close(mq_parent_fd_);
      mq_unlink(mq_parent_name_.c_str());
      mq_parent_fd_ = (mqd_t)-1;
    }

    check_should_exit();
  }
}

void BridgeGenerator::check_connection_demand()
{
  std::vector<std::string> bridges_to_remove;

  {
    std::lock_guard<std::mutex> lock(executor_mutex_);

    for (auto it = active_bridges_.begin(); it != active_bridges_.end(); ++it) {
      const std::string & unique_key = it->first;

      if (unique_key.size() <= 4) continue;

      std::string topic_name = unique_key.substr(0, unique_key.length() - 4);
      bool is_r2a = (unique_key.rfind("_R2A") != std::string::npos);
      std::string reverse_key = topic_name + (is_r2a ? "_A2R" : "_R2A");
      int threshold = (active_bridges_.count(reverse_key) > 0) ? 1 : 0;

      int count = get_agnocast_connection_count(topic_name, is_r2a);
      if (count < 0) {
        RCLCPP_WARN(
          logger_, "GC: Failed to get connection count for '%s': %s", topic_name.c_str(),
          strerror(errno));
        continue;
      }

      if (count <= threshold) {
        RCLCPP_INFO(
          logger_, "Bridge '%s' unused (Count:%d, Threshold:%d). Queued for removal.",
          unique_key.c_str(), count, threshold);
        bridges_to_remove.push_back(unique_key);
      }
    }

    for (const auto & key : bridges_to_remove) {
      remove_bridge_node_locked(key);
    }
  }
}

void BridgeGenerator::check_should_exit()
{
  if (!is_parent_alive_ && active_bridges_.empty()) {
    shutdown_requested_ = true;

    if (executor_) {
      executor_->cancel();
    }
  }
}

void BridgeGenerator::create_bridge_safely(const MqMsgBridge & req, const std::string & unique_key)
{
  load_and_add_node(req, unique_key);

  if (active_bridges_.count(unique_key)) {
    RCLCPP_INFO(logger_, "Bridge '%s' created successfully.", unique_key.c_str());
    return;
  }

  RCLCPP_WARN(logger_, "Failed to create bridge '%s'. Rolling back...", unique_key.c_str());

  std::string topic_name = req.target.topic_name;
  bool is_r2a = (req.direction == BridgeDirection::ROS2_TO_AGNOCAST);
  std::string reverse_key = topic_name + (is_r2a ? "_A2R" : "_R2A");

  if (active_bridges_.count(reverse_key) == 0) {
    unregister_from_kernel(topic_name);
  } else {
    RCLCPP_INFO(
      logger_, "Rollback: Skipped kernel unregister (reverse bridge '%s' is active).",
      reverse_key.c_str());
  }
}

void BridgeGenerator::remove_bridge_node_locked(const std::string & unique_key)
{
  if (active_bridges_.count(unique_key) == 0) {
    return;
  }
  active_bridges_.erase(unique_key);
  RCLCPP_INFO(logger_, "Removed bridge entry: %s", unique_key.c_str());

  const size_t suffix_len = 4;
  if (unique_key.size() <= suffix_len) return;

  std::string topic_name = unique_key.substr(0, unique_key.length() - suffix_len);
  bool is_r2a = (unique_key.compare(unique_key.length() - suffix_len, suffix_len, "_R2A") == 0);

  std::string reverse_key = topic_name + (is_r2a ? "_A2R" : "_R2A");

  if (active_bridges_.count(reverse_key) == 0) {
    unregister_from_kernel(topic_name);
  }

  check_should_exit();
}

void BridgeGenerator::load_and_add_node(const MqMsgBridge & req, const std::string & unique_key)
{
  auto [entry_func, lib_handle] = resolve_factory_function(req, unique_key);

  if (!entry_func) {
    const char * err = dlerror();
    RCLCPP_ERROR(
      logger_, "Failed to resolve factory for '%s': %s", unique_key.c_str(),
      err ? err : "Unknown error");
    return;
  }

  auto bridge = create_bridge_instance(entry_func, lib_handle, req.target);

  if (bridge) {
    active_bridges_[unique_key] = bridge;
    RCLCPP_INFO(logger_, "Bridge '%s' created.", unique_key.c_str());
  } else {
    RCLCPP_ERROR(logger_, "Factory returned null for '%s' (Creation failed)", unique_key.c_str());
  }
}

std::pair<void *, uintptr_t> BridgeGenerator::load_library_base(
  const char * lib_path, const char * symbol_name)
{
  void * handle = nullptr;

  if (std::strcmp(symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    handle = dlopen(NULL, RTLD_NOW);
  } else {
    handle = dlopen(lib_path, RTLD_NOW | RTLD_LOCAL);
  }

  if (!handle) {
    return {nullptr, 0};
  }

  struct link_map * map = static_cast<struct link_map *>(handle);
  return {handle, map->l_addr};
}

std::pair<BridgeFn, std::shared_ptr<void>> BridgeGenerator::resolve_factory_function(
  const MqMsgBridge & req, const std::string & unique_key)
{
  auto it = cached_factories_.find(unique_key);
  if (it != cached_factories_.end()) {
    RCLCPP_INFO(logger_, "Cache hit for '%s'", unique_key.c_str());
    return it->second;
  }

  dlerror();
  auto [raw_handle, base_addr] =
    load_library_base(req.factory.shared_lib_path, req.factory.symbol_name);

  if (base_addr == 0 && req.factory.fn_offset == 0) {
    if (raw_handle) dlclose(raw_handle);
    return {nullptr, nullptr};
  }

  std::shared_ptr<void> lib_handle_ptr(raw_handle, [](void * h) {
    if (h) dlclose(h);
  });

  BridgeFn entry_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset);

  cached_factories_[unique_key] = {entry_func, lib_handle_ptr};

  if (req.factory.fn_offset_reverse != 0) {
    std::string reverse_key = req.target.topic_name;
    reverse_key += (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_A2R" : "_R2A";

    BridgeFn reverse_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset_reverse);
    cached_factories_[reverse_key] = {reverse_func, lib_handle_ptr};
  }

  return {entry_func, lib_handle_ptr};
}

std::shared_ptr<void> BridgeGenerator::create_bridge_instance(
  BridgeFn entry_func, std::shared_ptr<void> lib_handle, const BridgeTargetInfo & target)
{
  try {
    auto bridge_resource = entry_func(container_node_, target);
    if (!bridge_resource) return nullptr;

    if (lib_handle) {
      using BundleType = std::pair<std::shared_ptr<void>, std::shared_ptr<void>>;
      auto bundle = std::make_shared<BundleType>(lib_handle, bridge_resource);
      return std::shared_ptr<void>(bundle, bridge_resource.get());
    } else {
      return bridge_resource;
    }
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "Exception in factory: %s", e.what());
    return nullptr;
  }
}

void BridgeGenerator::send_delegate_request(pid_t target_pid, const MqMsgBridge & req)
{
  std::string mq_name = create_mq_name_for_bridge_child(target_pid);

  mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY | O_CLOEXEC);

  if (mq == (mqd_t)-1) {
    RCLCPP_WARN(logger_, "Failed to open MQ for delegate PID %d: %s", target_pid, strerror(errno));
    return;
  }

  if (mq_send(mq, reinterpret_cast<const char *>(&req), sizeof(req), 0) < 0) {
    if (errno == EAGAIN) {
      RCLCPP_WARN(logger_, "Delegate MQ full for PID %d (Message dropped)", target_pid);
    } else {
      RCLCPP_ERROR(logger_, "mq_send failed to PID %d: %s", target_pid, strerror(errno));
    }
  }

  mq_close(mq);
}

void BridgeGenerator::unregister_from_kernel(const std::string & topic_name)
{
  struct ioctl_bridge_args args;
  std::memset(&args, 0, sizeof(args));
  args.pid = getpid();

  snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", topic_name.c_str());

  if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
    RCLCPP_INFO(logger_, "Unregistered bridge owner for '%s'", topic_name.c_str());
  } else {
    RCLCPP_WARN(
      logger_, "Failed to unregister bridge owner for '%s': %s", topic_name.c_str(),
      strerror(errno));
  }
}

int BridgeGenerator::get_agnocast_connection_count(const std::string & topic_name, bool is_r2a)
{
  int ret = -1;
  uint32_t count = 0;

  if (is_r2a) {
    union ioctl_get_subscriber_num_args args;
    std::memset(&args, 0, sizeof(args));
    args.topic_name = {topic_name.c_str(), topic_name.size()};

    ret = ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &args);
    count = args.ret_subscriber_num;
  } else {
    union ioctl_get_publisher_num_args args;
    std::memset(&args, 0, sizeof(args));
    args.topic_name = {topic_name.c_str(), topic_name.size()};

    ret = ioctl(agnocast_fd, AGNOCAST_GET_PUBLISHER_NUM_CMD, &args);
    count = args.ret_publisher_num;
  }

  if (ret != 0) {
    return -1;
  }
  return static_cast<int>(count);
}

}  // namespace agnocast

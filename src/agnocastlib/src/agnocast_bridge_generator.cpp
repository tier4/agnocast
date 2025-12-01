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

void BridgeGenerator::handle_epoll_events(const struct epoll_event * events, int count)
{
  for (int i = 0; i < count; ++i) {
    int fd = events[i].data.fd;

    if (fd == mq_parent_fd_) {
      handle_parent_mq_event();
    } else if (fd == mq_child_fd_) {
      handle_child_mq_event();
    } else if (fd == signal_fd_) {
      handle_signal_event();
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

void BridgeGenerator::handle_parent_mq_event()
{
  MqMsgBridge req;
  while (mq_receive(mq_parent_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
    // アクセス変更: req.target.topic_name
    std::string unique_key = req.target.topic_name;
    // アクセス変更: req.direction
    switch (req.direction) {
      case BridgeDirection::ROS2_TO_AGNOCAST:
        unique_key += "_R2A";
        break;
      case BridgeDirection::AGNOCAST_TO_ROS2:
        unique_key += "_A2R";
        break;
      default:
        continue;
    }

    std::lock_guard<std::mutex> lock(executor_mutex_);

    if (active_bridges_.count(unique_key)) {
      continue;
    }

    // オーナー登録試行
    struct ioctl_bridge_args args;
    std::memset(&args, 0, sizeof(args));
    args.pid = getpid();
    // アクセス変更: req.target.topic_name
    snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", req.target.topic_name);

    if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &args) == 0) {
      load_and_add_node(req, unique_key);
      if (active_bridges_.count(unique_key)) {
        RCLCPP_INFO(logger_, "Bridge '%s' created via delegation (Ref: 1)", unique_key.c_str());
      } else {
        RCLCPP_WARN(logger_, "Failed to create bridge '%s' via delegation.", unique_key.c_str());
        // unregister bridge owner
        struct ioctl_bridge_args args;
        std::memset(&args, 0, sizeof(args));
        args.pid = getpid();
        snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", req.target.topic_name);
        if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
          RCLCPP_INFO(
            logger_, "Unregistered bridge owner for failed delegation '%s'", unique_key.c_str());
        } else {
          RCLCPP_ERROR(
            logger_, "Failed to unregister bridge owner for '%s': %s", unique_key.c_str(),
            strerror(errno));
        }
      }
    } else if (errno == EEXIST) {
      union ioctl_get_bridge_pid_args pid_args;
      std::memset(&pid_args, 0, sizeof(pid_args));
      snprintf(pid_args.topic_name, MAX_TOPIC_NAME_LEN, "%s", req.target.topic_name);

      if (ioctl(agnocast_fd, AGNOCAST_GET_BRIDGE_PID_CMD, &pid_args) == 0) {
        pid_t owner_pid = pid_args.ret_pid;
        send_delegate_request(owner_pid, req);
        // active_bridges_[unique_key] = nullptr;
        RCLCPP_INFO(
          logger_, "Delegated bridge '%s' to owner PID %d", unique_key.c_str(), owner_pid);
      } else {
        RCLCPP_ERROR(logger_, "Failed to get owner PID for '%s'", unique_key.c_str());
      }
    } else {
      RCLCPP_ERROR(logger_, "Register bridge failed: %s", strerror(errno));
    }
  }
}

void BridgeGenerator::handle_child_mq_event()
{
  MqMsgBridge req;
  while (mq_receive(mq_child_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
    // アクセス変更: req.target.topic_name
    std::string unique_key = req.target.topic_name;
    // アクセス変更: req.direction
    switch (req.direction) {
      case BridgeDirection::ROS2_TO_AGNOCAST:
        unique_key += "_R2A";
        break;
      case BridgeDirection::AGNOCAST_TO_ROS2:
        unique_key += "_A2R";
        break;
      default:
        continue;
    }

    std::lock_guard<std::mutex> lock(executor_mutex_);

    if (active_bridges_.count(unique_key)) {
      RCLCPP_INFO(
        logger_, "Remote delegate request for '%s', but already exists. Ignoring...",
        unique_key.c_str());
    } else {
      RCLCPP_INFO(logger_, "First remote request for '%s'. Creating...", unique_key.c_str());
      load_and_add_node(req, unique_key);

      if (active_bridges_.count(unique_key)) {
        RCLCPP_INFO(logger_, "Bridge '%s' created via delegation (Ref: 1)", unique_key.c_str());
      } else {
        RCLCPP_WARN(logger_, "Failed to create bridge '%s' via delegation.", unique_key.c_str());
        // unregister bridge owner
        struct ioctl_bridge_args args;
        std::memset(&args, 0, sizeof(args));
        args.pid = getpid();
        snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", req.target.topic_name);
        if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
          RCLCPP_INFO(
            logger_, "Unregistered bridge owner for failed delegation '%s'", unique_key.c_str());
        } else {
          RCLCPP_ERROR(
            logger_, "Failed to unregister bridge owner for '%s': %s", unique_key.c_str(),
            strerror(errno));
        }
      }
    }
  }
}

void BridgeGenerator::handle_signal_event()
{
  struct signalfd_siginfo fdsi;
  ssize_t s = read(signal_fd_, &fdsi, sizeof(struct signalfd_siginfo));
  if (s != sizeof(struct signalfd_siginfo)) return;

  if (fdsi.ssi_signo == SIGTERM || fdsi.ssi_signo == SIGINT) {
    shutdown_requested_ = true;
    if (executor_) {
      executor_->cancel();
    }
  }
}

void BridgeGenerator::load_and_add_node(const MqMsgBridge & req, const std::string & unique_key)
{
  BridgeFn entry_func = nullptr;
  std::shared_ptr<void> lib_handle_ptr = nullptr;

  dlerror();

  // 1. キャッシュ検索
  auto it = cached_factories_.find(unique_key);
  if (it != cached_factories_.end()) {
    entry_func = it->second.first;
    lib_handle_ptr = it->second.second;
    RCLCPP_INFO(logger_, "Cache hit for '%s'", unique_key.c_str());
  } else {
    // 2. 新規ロード (キャッシュミス時 / DELEGATE含む)
    void * raw_handle = nullptr;
    uintptr_t base_addr = 0;

    // アクセス変更: req.factory...
    if (std::strcmp(req.factory.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
      void * handle = dlopen(NULL, RTLD_NOW);
      if (handle) {
        struct link_map * map = static_cast<struct link_map *>(handle);
        base_addr = map->l_addr;
      }
    } else {
      void * handle = dlopen(req.factory.shared_lib_path, RTLD_NOW | RTLD_LOCAL);
      if (handle) {
        raw_handle = handle;
        struct link_map * map = static_cast<struct link_map *>(handle);
        base_addr = map->l_addr;
      }
    }

    if (base_addr != 0 || req.factory.fn_offset != 0) {
      // RAIIハンドルの作成
      if (raw_handle) {
        lib_handle_ptr.reset(raw_handle, [](void * h) {
          if (h) dlclose(h);
        });
      }

      // アクセス変更: req.factory.fn_offset
      entry_func = reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset);

      // キャッシュへ登録
      cached_factories_[unique_key] = {entry_func, lib_handle_ptr};

      // 逆方向キャッシュ
      if (req.factory.fn_offset_reverse != 0) {
        // アクセス変更: req.target.topic_name, req.direction
        std::string reverse_key = req.target.topic_name;
        if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST)
          reverse_key += "_A2R";
        else
          reverse_key += "_R2A";

        BridgeFn reverse_func =
          reinterpret_cast<BridgeFn>(base_addr + req.factory.fn_offset_reverse);
        cached_factories_[reverse_key] = {reverse_func, lib_handle_ptr};
      }
    }
  }

  // 3. 実行と登録
  if (!entry_func) {
    RCLCPP_ERROR(logger_, "Entry function is null for '%s' (Load failed)", unique_key.c_str());
    return;
  }

  try {
    // アクセス変更: req.target (BridgeTargetInfo) をファクトリへ渡す
    auto bridge_resource = entry_func(container_node_, req.target);

    if (bridge_resource) {
      // エイリアスコンストラクタによる寿命結合
      if (lib_handle_ptr) {
        using BundleType = std::pair<std::shared_ptr<void>, std::shared_ptr<void>>;
        auto bundle = std::make_shared<BundleType>(lib_handle_ptr, bridge_resource);
        std::shared_ptr<void> tied_bridge(bundle, bridge_resource.get());
        active_bridges_[unique_key] = tied_bridge;
      } else {
        active_bridges_[unique_key] = bridge_resource;
      }
      RCLCPP_INFO(logger_, "Bridge '%s' created.", unique_key.c_str());
    }
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "Exception creating bridge '%s': %s", unique_key.c_str(), e.what());
  }
}

void BridgeGenerator::remove_bridge_node(const std::string & unique_key)
{
  if (active_bridges_.count(unique_key)) {
    active_bridges_.erase(unique_key);
    RCLCPP_INFO(logger_, "Removed bridge entry: %s", unique_key.c_str());

    std::string topic_name = unique_key.substr(0, unique_key.length() - 4);
    std::string reverse_key;
    if (unique_key.rfind("_R2A") != std::string::npos)
      reverse_key = topic_name + "_A2R";
    else
      reverse_key = topic_name + "_R2A";

    if (active_bridges_.count(reverse_key) == 0) {
      struct ioctl_bridge_args args;
      std::memset(&args, 0, sizeof(args));
      args.pid = getpid();
      snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", topic_name.c_str());

      if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
        RCLCPP_INFO(logger_, "Unregistered bridge owner for '%s'", topic_name.c_str());
      }
    }

    // ★ 親プロセス切り離しロジック
    check_should_exit();
  }
}

void BridgeGenerator::send_delegate_request(pid_t target_pid, const MqMsgBridge & original_req)
{
  std::string mq_name = create_mq_name_for_bridge_child(target_pid);
  mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY);

  if (mq == (mqd_t)-1) {
    RCLCPP_WARN(logger_, "Failed to open MQ for delegate PID %d: %s", target_pid, strerror(errno));
    return;
  }

  MqMsgBridge msg = original_req;

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) < 0) {
    RCLCPP_ERROR(logger_, "mq_send failed to PID %d: %s", target_pid, strerror(errno));
  }
  mq_close(mq);
}

void BridgeGenerator::check_connection_demand()
{
  std::vector<std::string> bridges_to_remove;

  {
    // マップ操作とカーネル問い合わせの間、整合性を保つためにロック
    std::lock_guard<std::mutex> lock(executor_mutex_);

    for (auto it = active_bridges_.begin(); it != active_bridges_.end(); ++it) {
      const std::string & unique_key = it->first;

      // キー解析 ("/topic_R2A" -> "/topic", is_r2a=true)
      std::string topic_name = unique_key.substr(0, unique_key.length() - 4);
      bool is_r2a = (unique_key.rfind("_R2A") != std::string::npos);

      // -----------------------------------------------------
      // 1. 閾値 (Threshold) の決定
      // -----------------------------------------------------
      // 逆方向のブリッジ（ペア）が同一プロセス内に存在するか確認
      std::string reverse_key = topic_name + (is_r2a ? "_A2R" : "_R2A");
      bool has_reverse = (active_bridges_.count(reverse_key) > 0);
      uint32_t threshold = has_reverse ? 1 : 0;

      // -----------------------------------------------------
      // 2. カーネルからのカウント取得
      // -----------------------------------------------------
      uint32_t count = 0;
      int ret = -1;

      if (is_r2a) {
        // R2A (自分はPub) -> Agnocast Subscriber数を確認
        union ioctl_get_subscriber_num_args args;
        std::memset(&args, 0, sizeof(args));
        // 生のトピック名を使用
        args.topic_name = {topic_name.c_str(), topic_name.size()};

        ret = ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &args);
        if (ret == 0) {
          count = args.ret_subscriber_num;
        }
      } else {
        // A2R (自分はSub) -> Agnocast Publisher数を確認
        union ioctl_get_publisher_num_args args;
        std::memset(&args, 0, sizeof(args));
        args.topic_name = {topic_name.c_str(), topic_name.size()};

        ret = ioctl(agnocast_fd, AGNOCAST_GET_PUBLISHER_NUM_CMD, &args);
        if (ret == 0) {
          count = args.ret_publisher_num;
        }
      }

      if (ret < 0) {
        RCLCPP_WARN(
          logger_, "Failed to get connection count for '%s': %s", topic_name.c_str(),
          strerror(errno));
        continue;  // エラー時は安全側に倒して削除しない
      }

      // -----------------------------------------------------
      // 3. 判定
      // -----------------------------------------------------
      // 外部の利用者がいなければ (Count <= Threshold)、削除対象に追加
      if (count <= threshold) {
        RCLCPP_INFO(
          logger_, "Bridge '%s' unused (Count:%d, Threshold:%d). Queued for removal.",
          unique_key.c_str(), count, threshold);
        bridges_to_remove.push_back(unique_key);
      }
    }

    for (const auto & key : bridges_to_remove) {
      remove_bridge_node(key);
    }
  }
}

}  // namespace agnocast
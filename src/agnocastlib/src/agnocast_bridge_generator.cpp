#include "agnocast/agnocast_bridge_generator.hpp"

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <link.h>
#include <sys/epoll.h>
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
  // 親プロセスの生存確認
  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  // --- ROS 2 コンテキストのリセットと再初期化 ---
  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  rclcpp::InitOptions init_options;
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  logger_ = rclcpp::get_logger("agnocast_bridge_generator");

  if (!agnocast_heaphook_init_daemon()) {
    RCLCPP_ERROR(logger_, "Heaphook init FAILED.");
  }

  setup_mq();
  setup_signals();
  setup_epoll();
}

BridgeGenerator::~BridgeGenerator()
{
  if (epoll_fd_ != -1) close(epoll_fd_);
  if (signal_fd_ != -1) close(signal_fd_);

  if (mq_fd_ != (mqd_t)-1) mq_close(mq_fd_);
  if (!mq_name_.empty()) mq_unlink(mq_name_.c_str());

  if (executor_) {
    executor_->cancel();
  }
  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  RCLCPP_INFO(logger_, "Agnocast Bridge Generator shutting down.");

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void BridgeGenerator::setup_mq()
{
  mq_name_ = create_mq_name_for_bridge(target_pid_);
  mq_unlink(mq_name_.c_str());

  struct mq_attr attr{};
  attr.mq_maxmsg = 10;
  attr.mq_msgsize = sizeof(MqMsgBridge);

  mq_fd_ = mq_open(mq_name_.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK, 0644, &attr);
  if (mq_fd_ == (mqd_t)-1) {
    throw std::runtime_error("MQ open failed: " + std::string(strerror(errno)));
  }
}

void BridgeGenerator::setup_signals()
{
  sigset_t mask;
  sigemptyset(&mask);
  sigaddset(&mask, SIGTERM);
  sigaddset(&mask, SIGINT);

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

  struct epoll_event ev_mq{};
  ev_mq.events = EPOLLIN;
  ev_mq.data.fd = mq_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_fd_, &ev_mq) == -1) {
    throw std::runtime_error("epoll_ctl (MQ) failed");
  }

  struct epoll_event ev_sig{};
  ev_sig.events = EPOLLIN;
  ev_sig.data.fd = signal_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, signal_fd_, &ev_sig) == -1) {
    throw std::runtime_error("epoll_ctl (Signal) failed");
  }
}

void BridgeGenerator::run()
{
  // 1. コンテナノード作成
  std::string node_name = "agnocast_bridge_container_" + std::to_string(getpid());
  container_node_ = std::make_shared<rclcpp::Node>(node_name);

  // 2. Executor生成
  executor_ =
    std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(rclcpp::ExecutorOptions(), 0, 0);

  // 3. コンテナノード追加
  executor_->add_node(container_node_);

  // スピン用スレッド開始
  executor_thread_ = std::thread([this]() {
    try {
      this->executor_->spin();
    } catch (const std::exception & e) {
      RCLCPP_FATAL(logger_, "Executor Thread CRASHED: %s", e.what());
    } catch (...) {
      RCLCPP_FATAL(logger_, "Executor Thread CRASHED (Unknown)");
    }
  });

  // メインループ
  constexpr int MAX_EVENTS = 10;
  struct epoll_event events[MAX_EVENTS];

  while (!shutdown_requested_ && rclcpp::ok()) {
    if (kill(target_pid_, 0) != 0) {
      RCLCPP_WARN(logger_, "Parent process %d is dead. Shutting down.", target_pid_);
      break;
    }

    int n = epoll_wait(epoll_fd_, events, MAX_EVENTS, 1000);

    if (n < 0) {
      if (errno == EINTR) continue;
      break;
    }

    for (int i = 0; i < n; ++i) {
      int fd = events[i].data.fd;
      if (fd == mq_fd_) {
        handle_mq_event();
      } else if (fd == signal_fd_) {
        handle_signal_event();
      }
    }
  }
}

void BridgeGenerator::handle_mq_event()
{
  MqMsgBridge req;
  while (mq_receive(mq_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
    // ユニークキー生成
    std::string unique_key = req.args.topic_name;
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

    if (
      req.command == BridgeCommand::CREATE_BRIDGE ||
      req.command == BridgeCommand::DELEGATE_CREATE) {
      // --- CREATE / DELEGATE ---
      if (bridge_ref_counts_[unique_key] == 0) {
        load_and_add_node(req, unique_key);
      } else {
        RCLCPP_INFO(
          logger_, "Bridge '%s' ref++ (%d)", unique_key.c_str(),
          bridge_ref_counts_[unique_key] + 1);
      }
      bridge_ref_counts_[unique_key]++;

    } else if (req.command == BridgeCommand::REMOVE_BRIDGE) {
      //-- -REMOVE---
      if (bridge_ref_counts_[unique_key] > 0) {
        bridge_ref_counts_[unique_key]--;

        if (bridge_ref_counts_[unique_key] == 0) {
          remove_bridge_node(unique_key);
        } else {
          RCLCPP_INFO(
            logger_, "Bridge '%s' ref-- (%d)", unique_key.c_str(), bridge_ref_counts_[unique_key]);
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
  void * handle_to_store = nullptr;
  dlerror();  // エラークリア

  // ---------------------------------------------------------
  // 1. 委譲 (Delegate) の場合
  // ---------------------------------------------------------
  if (req.command == BridgeCommand::DELEGATE_CREATE) {
    auto it = cached_factories_.find(unique_key);
    if (it != cached_factories_.end()) {
      entry_func = it->second;
      RCLCPP_INFO(logger_, "Delegated creation using cached factory for '%s'", unique_key.c_str());
    } else {
      RCLCPP_ERROR(
        logger_, "Delegation failed: No cached factory found for '%s'", unique_key.c_str());
      return;
    }
  }
  // ---------------------------------------------------------
  // 2. 新規ロード (New Load) の場合
  // ---------------------------------------------------------
  else {
    uintptr_t base_addr = 0;

    // A. メイン実行ファイル内のシンボルの場合
    if (std::strcmp(req.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
      // メイン実行ファイル自身のハンドルを取得
      void * handle = dlopen(NULL, RTLD_NOW);
      if (!handle) {
        RCLCPP_ERROR(logger_, "dlopen(NULL) failed: %s", dlerror());
        return;
      }
      // ハンドルからリンクマップを取得してベースアドレスを取り出す
      struct link_map * map = static_cast<struct link_map *>(handle);
      base_addr = map->l_addr;

      // dlopen(NULL) のハンドルは通常 close しなくても良いが、
      // 整合性のため handle_to_store に入れても良いし、入れなくても良い。
      // ここでは明示的に管理しない(closeすると困る場合があるため)。
    }
    // B. 共有ライブラリの場合
    else {
      void * handle = dlopen(req.shared_lib_path, RTLD_NOW);
      if (!handle) {
        RCLCPP_ERROR(logger_, "dlopen failed: %s", dlerror());
        return;
      }
      handle_to_store = handle;

      // ハンドルからリンクマップを取得してベースアドレスを取り出す
      struct link_map * map = static_cast<struct link_map *>(handle);
      base_addr = map->l_addr;
    }

    // ★重要: オフセットから関数ポインタを復元
    entry_func = reinterpret_cast<BridgeFn>(base_addr + req.fn_offset);

    // ★重要: 逆方向の関数ポインタも復元してキャッシュ
    if (req.fn_offset_reverse != 0) {
      std::string reverse_key = req.args.topic_name;
      if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
        reverse_key += "_A2R";
      } else {
        reverse_key += "_R2A";
      }

      // ベースアドレス + 逆方向オフセット
      BridgeFn reverse_func = reinterpret_cast<BridgeFn>(base_addr + req.fn_offset_reverse);

      cached_factories_[reverse_key] = reverse_func;
      RCLCPP_INFO(logger_, "Cached reverse factory for '%s'", reverse_key.c_str());
    }
  }

  // ---------------------------------------------------------
  // 3. 実行と登録
  // ---------------------------------------------------------
  if (!entry_func) {
    RCLCPP_ERROR(logger_, "Entry function is null for '%s'", unique_key.c_str());
    if (handle_to_store) dlclose(handle_to_store);
    return;
  }

  try {
    auto bridge_resource = entry_func(container_node_, req.args);

    if (bridge_resource) {
      active_bridges_[unique_key] = bridge_resource;

      if (handle_to_store) {
        dl_handles_.push_back(std::shared_ptr<void>(handle_to_store, [](void * h) {
          if (h) dlclose(h);
        }));
      }
      RCLCPP_INFO(
        logger_, "Started bridge: %s (Delegated: %d)", unique_key.c_str(),
        (req.command == BridgeCommand::DELEGATE_CREATE));
    }
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "Exception creating bridge '%s': %s", unique_key.c_str(), e.what());
    if (handle_to_store) dlclose(handle_to_store);
  } catch (...) {
    RCLCPP_ERROR(logger_, "Unknown exception creating bridge '%s'.", unique_key.c_str());
    if (handle_to_store) dlclose(handle_to_store);
  }
}

void BridgeGenerator::remove_bridge_node(const std::string & unique_key)
{
  if (active_bridges_.count(unique_key)) {
    // 1. ブリッジ実体を削除 (shared_ptr破棄 -> ROSノード削除等)
    active_bridges_.erase(unique_key);
    RCLCPP_INFO(logger_, "Removed bridge: %s", unique_key.c_str());

    // 2. カーネル登録解除の判定 (オーナー権限の放棄)
    // トピック名 (例: "/my_topic") と 逆方向キー を特定
    std::string topic_name;
    std::string reverse_key;

    // 末尾が _R2A か _A2R かで分岐
    if (unique_key.rfind("_R2A") != std::string::npos) {
      topic_name = unique_key.substr(0, unique_key.length() - 4);
      reverse_key = topic_name + "_A2R";
    } else if (unique_key.rfind("_A2R") != std::string::npos) {
      topic_name = unique_key.substr(0, unique_key.length() - 4);
      reverse_key = topic_name + "_R2A";
    } else {
      // 想定外のキー
      return;
    }

    // ★重要: 逆方向も存在しない(=誰も使っていない)なら、オーナー権限を放棄
    if (active_bridges_.count(reverse_key) == 0) {
      struct ioctl_bridge_args args;
      std::memset(&args, 0, sizeof(args));
      args.pid = target_pid_;  // 自分(オーナー)のPID
      safe_strncpy(args.topic_name, topic_name.c_str(), MAX_TOPIC_NAME_LEN);

      if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
        RCLCPP_INFO(logger_, "Unregistered bridge owner for '%s'", topic_name.c_str());
      } else {
        // 他のプロセスがすぐに再登録した可能性もあるのでエラーログは控えめに
        RCLCPP_DEBUG(logger_, "Unregister bridge owner: %s", strerror(errno));
      }

      // キャッシュもクリア (再作成時はまた送られてくるので消してOK)
      cached_factories_.erase(unique_key);
      cached_factories_.erase(reverse_key);
    }
  }
}

}  // namespace agnocast
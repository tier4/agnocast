#include "agnocast/agnocast_bridge_generator.hpp"

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_utils.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <link.h>
#include <mqueue.h>
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

  if (mq_parent_fd_ != (mqd_t)-1) mq_close(mq_parent_fd_);
  if (!mq_parent_name_.empty()) mq_unlink(mq_parent_name_.c_str());

  if (mq_child_fd_ != (mqd_t)-1) mq_close(mq_child_fd_);
  if (!mq_child_name_.empty()) mq_unlink(mq_child_name_.c_str());

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
  struct mq_attr attr{};
  attr.mq_maxmsg = 10;
  attr.mq_msgsize = sizeof(MqMsgBridge);

  // 1. Parent MQ (Control Plane)
  // 親プロセス(target_pid_)が書き込み、自分が読み込む
  mq_parent_name_ = create_mq_name_for_bridge_parent(target_pid_);
  mq_unlink(mq_parent_name_.c_str());  // 掃除

  mq_parent_fd_ = mq_open(mq_parent_name_.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK, 0644, &attr);
  if (mq_parent_fd_ == (mqd_t)-1) {
    throw std::runtime_error("Parent MQ open failed: " + std::string(strerror(errno)));
  }

  // 2. Child MQ (Delegation Plane)
  // 他のGeneratorが書き込み、自分が読み込む (自分のPIDを使用)
  mq_child_name_ = create_mq_name_for_bridge_child(getpid());
  mq_unlink(mq_child_name_.c_str());

  mq_child_fd_ = mq_open(mq_child_name_.c_str(), O_CREAT | O_RDONLY | O_NONBLOCK, 0644, &attr);
  if (mq_child_fd_ == (mqd_t)-1) {
    throw std::runtime_error("Child MQ open failed: " + std::string(strerror(errno)));
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

  // Parent MQ 監視登録
  struct epoll_event ev_parent{};
  ev_parent.events = EPOLLIN;
  ev_parent.data.fd = mq_parent_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_parent_fd_, &ev_parent) == -1) {
    throw std::runtime_error("epoll_ctl (Parent MQ) failed");
  }

  // Child MQ 監視登録
  struct epoll_event ev_child{};
  ev_child.events = EPOLLIN;
  ev_child.data.fd = mq_child_fd_;
  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_child_fd_, &ev_child) == -1) {
    throw std::runtime_error("epoll_ctl (Child MQ) failed");
  }

  // Signal 監視登録
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
      if (fd == mq_parent_fd_) {
        handle_parent_mq_event();
      } else if (fd == mq_child_fd_) {
        handle_child_mq_event();
      } else if (fd == signal_fd_) {
        handle_signal_event();
      }
    }
  }
}

// =========================================================================
// Event Handler 1: 親プロセスからのコマンド (Local Control)
// =========================================================================
void BridgeGenerator::handle_parent_mq_event()
{
  MqMsgBridge req;
  while (mq_receive(mq_parent_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
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

    // --- CREATE_BRIDGE (親から「使いたい」と言われた) ---
    if (req.command == BridgeCommand::CREATE_BRIDGE) {
      // 1. 既に自分が管理下(オーナー or 委譲済み)にある場合
      if (active_bridges_.count(unique_key)) {
        bridge_ref_counts_[unique_key]++;
        RCLCPP_INFO(
          logger_, "Bridge '%s' local ref++ (Total: %d)", unique_key.c_str(),
          bridge_ref_counts_[unique_key]);
        continue;
      }

      // 2. カーネル登録を試みる (オーナーになりたい)
      struct ioctl_bridge_args args;
      std::memset(&args, 0, sizeof(args));
      args.pid = getpid();  // ★自分のPIDで登録
      safe_strncpy(args.topic_name, req.args.topic_name, MAX_TOPIC_NAME_LEN);

      if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &args) == 0) {
        // === 成功: 自分がオーナー ===
        load_and_add_node(req, unique_key);
        bridge_ref_counts_[unique_key] = 1;
        RCLCPP_INFO(logger_, "Registered bridge owner for '%s'", unique_key.c_str());

      } else if (errno == EEXIST) {
        // === 失敗: 既に誰かがオーナー ===
        union ioctl_get_bridge_pid_args pid_args;
        std::memset(&pid_args, 0, sizeof(pid_args));
        safe_strncpy(pid_args.topic_name, req.args.topic_name, MAX_TOPIC_NAME_LEN);

        if (ioctl(agnocast_fd, AGNOCAST_GET_BRIDGE_PID_CMD, &pid_args) == 0) {
          pid_t owner_pid = pid_args.ret_pid;

          // オーナーの Global MQ へ委譲依頼を転送
          send_delegate_request(owner_pid, req);

          // 自分のローカル管理上は「存在するもの」として扱う (ただし実体はnullptr)
          active_bridges_[unique_key] = nullptr;
          bridge_ref_counts_[unique_key] = 1;

          RCLCPP_INFO(
            logger_, "Delegated bridge '%s' to owner PID %d", unique_key.c_str(), owner_pid);
        } else {
          RCLCPP_ERROR(logger_, "Failed to get owner PID for '%s'", unique_key.c_str());
        }
      } else {
        RCLCPP_ERROR(logger_, "Register bridge failed: %s", strerror(errno));
      }
    }
    // --- REMOVE_BRIDGE (親から「もういらない」と言われた) ---
    else if (req.command == BridgeCommand::REMOVE_BRIDGE) {
      if (active_bridges_.count(unique_key) > 0) {
        bridge_ref_counts_[unique_key]--;

        if (bridge_ref_counts_[unique_key] == 0) {
          remove_bridge_node(unique_key);
        } else {
          RCLCPP_INFO(
            logger_, "Bridge '%s' local ref-- (Total: %d)", unique_key.c_str(),
            bridge_ref_counts_[unique_key]);
        }
      }
    }
  }
}

void BridgeGenerator::handle_child_mq_event()
{
  MqMsgBridge req;
  while (mq_receive(mq_child_fd_, (char *)&req, sizeof(req), nullptr) > 0) {
    std::string unique_key = req.args.topic_name;
    // Suffix付与
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

    if (req.command == BridgeCommand::DELEGATE_CREATE) {
      // Case 1: 既に起動済み (Ref: N -> N+1)
      if (active_bridges_.count(unique_key) && active_bridges_[unique_key] != nullptr) {
        bridge_ref_counts_[unique_key]++;
        RCLCPP_INFO(
          logger_, "Bridge '%s' remote ref++ (Total: %d)", unique_key.c_str(),
          bridge_ref_counts_[unique_key]);
      }
      // Case 2: 未起動だがオーナー権限は持っているはず (Ref: 0 -> 1) ★修正箇所
      else {
        RCLCPP_INFO(
          logger_, "First remote request for '%s'. Creating from cache...", unique_key.c_str());

        // キャッシュ(cached_factories_)を使って作成を試みる
        // load_and_add_node は DELEGATE_CREATE
        // コマンドの場合、キャッシュを見に行く実装になっています
        load_and_add_node(req, unique_key);

        // 作成に成功したか確認
        if (active_bridges_.count(unique_key)) {
          bridge_ref_counts_[unique_key] = 1;
          RCLCPP_INFO(logger_, "Bridge '%s' created via delegation (Ref: 1)", unique_key.c_str());
        } else {
          // キャッシュがない = 本当にオーナーではない、あるいはバグ
          RCLCPP_WARN(
            logger_, "Failed to create bridge '%s' via delegation. (No cache found?)",
            unique_key.c_str());
        }
      }

    } else if (req.command == BridgeCommand::REMOVE_BRIDGE) {
      // (REMOVE処理は変更なし)
      if (active_bridges_.count(unique_key)) {
        if (bridge_ref_counts_[unique_key] > 0) {
          bridge_ref_counts_[unique_key]--;
          if (bridge_ref_counts_[unique_key] == 0) {
            remove_bridge_node(unique_key);
          } else {
            RCLCPP_INFO(
              logger_, "Bridge '%s' remote ref-- (Total: %d)", unique_key.c_str(),
              bridge_ref_counts_[unique_key]);
          }
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

// =========================================================================
// Logic: Load & Remove & Delegate Helper
// =========================================================================

void BridgeGenerator::load_and_add_node(const MqMsgBridge & req, const std::string & unique_key)
{
  BridgeFn entry_func = nullptr;
  void * handle_to_store = nullptr;
  dlerror();  // エラークリア

  // 1. 委譲(DELEGATE)によるキャッシュ利用
  // (今回は親から来たCREATEを即座に処理するフローが主だが、
  //  逆方向キャッシュを使う場合ここを通る)
  if (req.command == BridgeCommand::DELEGATE_CREATE) {
    // NOTE: DELEGATE経由でここに来るのは、自分がオーナーで逆方向を作る時など
    auto it = cached_factories_.find(unique_key);
    if (it != cached_factories_.end()) {
      entry_func = it->second;
    }
  }
  // 2. 新規ロード
  else {
    uintptr_t base_addr = 0;

    if (std::strcmp(req.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
      void * handle = dlopen(NULL, RTLD_NOW);
      if (handle) {
        struct link_map * map = static_cast<struct link_map *>(handle);
        base_addr = map->l_addr;
      }
    } else {
      void * handle = dlopen(req.shared_lib_path, RTLD_NOW);
      if (handle) {
        handle_to_store = handle;
        struct link_map * map = static_cast<struct link_map *>(handle);
        base_addr = map->l_addr;
      }
    }

    if (base_addr != 0 || req.fn_offset != 0) {
      entry_func = reinterpret_cast<BridgeFn>(base_addr + req.fn_offset);

      // 逆方向キャッシュ
      if (req.fn_offset_reverse != 0) {
        std::string reverse_key = req.args.topic_name;
        if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
          reverse_key += "_A2R";
        } else {
          reverse_key += "_R2A";
        }
        BridgeFn reverse_func = reinterpret_cast<BridgeFn>(base_addr + req.fn_offset_reverse);
        cached_factories_[reverse_key] = reverse_func;
      }
    }
  }

  // 3. 実行と登録
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
    }
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "Exception creating bridge '%s': %s", unique_key.c_str(), e.what());
    if (handle_to_store) dlclose(handle_to_store);
  }
}

void BridgeGenerator::remove_bridge_node(const std::string & unique_key)
{
  if (active_bridges_.count(unique_key)) {
    // 実体を持っているか(オーナーか)、委譲中か(nullptr)を確認
    bool is_owner = (active_bridges_[unique_key] != nullptr);

    // 1. ブリッジ管理削除
    active_bridges_.erase(unique_key);
    RCLCPP_INFO(logger_, "Removed bridge entry: %s", unique_key.c_str());

    if (is_owner) {
      // --- オーナーとしての削除処理 ---

      // カーネル登録解除の判定 (逆方向キーを確認)
      std::string topic_name;
      std::string reverse_key;
      if (unique_key.rfind("_R2A") != std::string::npos) {
        topic_name = unique_key.substr(0, unique_key.length() - 4);
        reverse_key = topic_name + "_A2R";
      } else {
        topic_name = unique_key.substr(0, unique_key.length() - 4);
        reverse_key = topic_name + "_R2A";
      }

      // 逆方向も誰も使っていなければオーナー権限放棄
      if (active_bridges_.count(reverse_key) == 0) {
        struct ioctl_bridge_args args;
        std::memset(&args, 0, sizeof(args));
        args.pid = getpid();
        safe_strncpy(args.topic_name, topic_name.c_str(), MAX_TOPIC_NAME_LEN);

        if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
          RCLCPP_INFO(logger_, "Unregistered bridge owner for '%s'", topic_name.c_str());
        }
        cached_factories_.erase(unique_key);
        cached_factories_.erase(reverse_key);
      }
    } else {
      // --- 委譲先への削除通知 ---
      // オーナーPIDを再取得して REMOVE を送る
      // (unique_key から トピック名を復元)
      std::string topic_name = unique_key.substr(0, unique_key.length() - 4);

      union ioctl_get_bridge_pid_args pid_args;
      std::memset(&pid_args, 0, sizeof(pid_args));
      safe_strncpy(pid_args.topic_name, topic_name.c_str(), MAX_TOPIC_NAME_LEN);

      if (ioctl(agnocast_fd, AGNOCAST_GET_BRIDGE_PID_CMD, &pid_args) == 0) {
        pid_t owner_pid = pid_args.ret_pid;

        // メッセージ作成 (REMOVE)
        MqMsgBridge msg = {};
        safe_strncpy(msg.args.topic_name, topic_name.c_str(), MAX_TOPIC_NAME_LEN);
        msg.command = BridgeCommand::REMOVE_BRIDGE;
        msg.direction = (unique_key.find("_R2A") != std::string::npos)
                          ? BridgeDirection::ROS2_TO_AGNOCAST
                          : BridgeDirection::AGNOCAST_TO_ROS2;

        send_delegate_request(owner_pid, msg);
        RCLCPP_INFO(logger_, "Sent remove request to owner PID %d", owner_pid);
      }
    }
  }
}

void BridgeGenerator::send_delegate_request(pid_t target_pid, const MqMsgBridge & original_req)
{
  // 相手(オーナー)の Global MQ (Child MQ) に送る
  std::string mq_name = create_mq_name_for_bridge_child(target_pid);
  mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY);

  if (mq == (mqd_t)-1) {
    RCLCPP_WARN(logger_, "Failed to open MQ for delegate PID %d: %s", target_pid, strerror(errno));
    return;
  }

  MqMsgBridge msg = original_req;
  // REMOVEの場合はそのまま送るが、CREATEの場合はDELEGATEに書き換える
  if (msg.command == BridgeCommand::CREATE_BRIDGE) {
    msg.command = BridgeCommand::DELEGATE_CREATE;
  }

  if (mq_send(mq, (const char *)&msg, sizeof(msg), 0) < 0) {
    RCLCPP_ERROR(logger_, "mq_send failed to PID %d: %s", target_pid, strerror(errno));
  }
  mq_close(mq);
}

}  // namespace agnocast
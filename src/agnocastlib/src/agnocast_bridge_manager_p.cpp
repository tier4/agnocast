#include "agnocast/agnocast_bridge_manager_p.hpp"

#include "agnocast/agnocast_bridge_utils.hpp"
#include "agnocast/agnocast_callback_isolated_executor.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "agnocast/agnocast_single_threaded_executor.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <mqueue.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <unistd.h>

#include <csignal>
#include <vector>

namespace agnocast
{

PerformanceBridgeManager::PerformanceBridgeManager()
: logger_(rclcpp::get_logger("agnocast_performance_bridge_manager")),
  event_loop_(logger_),
  loader_(logger_)
{
  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  rclcpp::InitOptions init_options{};
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  config_handler_ = std::make_unique<BridgeConfigP>(logger_);
  RCLCPP_INFO(logger_, "Bridge Manager initialized (PID: %d).", getpid());
}

PerformanceBridgeManager::~PerformanceBridgeManager()
{
  if (executor_) {
    executor_->cancel();
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  executor_.reset();
  container_node_.reset();
}

void PerformanceBridgeManager::run()
{
  constexpr int EVENT_LOOP_TIMEOUT_MS = 1000;
  int maintenance_counter = 0;

  std::string proc_name = "agno_br_" + std::to_string(getpid());
  prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0);

  start_ros_execution();

  event_loop_.set_peer_mq_handler([this](int fd) { this->on_mq_request(fd); });
  event_loop_.set_signal_handler([this]() { this->on_signal(); });
  event_loop_.set_reload_handler([this]() { this->on_reload(); });

  RCLCPP_INFO(logger_, "Performance Bridge Manager loop started.");

  while (!shutdown_requested_) {
    if (!event_loop_.spin_once(EVENT_LOOP_TIMEOUT_MS)) {
      RCLCPP_ERROR(logger_, "Event loop spin failed.");
      break;
    }

    if (++maintenance_counter >= 10) {
      cleanup_request_cache();
      maintenance_counter = 0;
    }

    check_and_remove_bridges();
    check_and_request_shutdown();
  }
}

void PerformanceBridgeManager::start_ros_execution()
{
  std::string node_name = "agnocast_bridge_node_" + std::to_string(getpid());
  container_node_ = std::make_shared<rclcpp::Node>(node_name);

  executor_ = select_executor();
  executor_->add_node(container_node_);

  executor_thread_ = std::thread([this]() {
    try {
      this->executor_->spin();
    } catch (const std::exception & e) {
      RCLCPP_ERROR(logger_, "Executor Thread CRASHED: %s", e.what());
    }
  });
}

std::unique_ptr<rclcpp::Executor> PerformanceBridgeManager::select_executor()
{
  const char * executor_type_env = std::getenv("AGNOCAST_EXECUTOR_TYPE");
  std::string executor_type = executor_type_env ? executor_type_env : "single";

  // 1. Multi Threaded
  if (executor_type == "multi") {
    size_t num_threads = 0;
    const char * thread_num_env = std::getenv("AGNOCAST_MULTI_THREAD_NUM");

    if (thread_num_env) {
      try {
        num_threads = std::stoul(thread_num_env);
      } catch (const std::exception & e) {
        RCLCPP_WARN(
          logger_,
          "Invalid AGNOCAST_MULTI_THREAD_NUM ('%s'). Using hardware concurrency. Error: %s",
          thread_num_env, e.what());
      }
    }

    if (num_threads == 0) {
      num_threads = std::thread::hardware_concurrency();
      if (num_threads == 0) {
        RCLCPP_WARN(logger_, "Could not detect hardware concurrency. Defaulting to 4 threads.");
        num_threads = 4;
      }
    }

    RCLCPP_INFO(logger_, "Using MultiThreadedAgnocastExecutor with %zu threads.", num_threads);
    rclcpp::ExecutorOptions options;
    return std::make_unique<agnocast::MultiThreadedAgnocastExecutor>(options, num_threads);
  }

  // 2. Callback Isolated
  else if (executor_type == "isolated") {
    RCLCPP_INFO(logger_, "Using CallbackIsolatedAgnocastExecutor.");
    return std::make_unique<agnocast::CallbackIsolatedAgnocastExecutor>();
  }

  // 3. Single Threaded (Default)
  RCLCPP_INFO(logger_, "Using SingleThreadedAgnocastExecutor.");
  return std::make_unique<agnocast::SingleThreadedAgnocastExecutor>();
}

void PerformanceBridgeManager::on_mq_request(int fd)
{
  std::vector<char> buffer(PERFORMANCE_BRIDGE_MQ_MESSAGE_SIZE);

  ssize_t bytes_read = mq_receive((mqd_t)fd, buffer.data(), buffer.size(), nullptr);

  if (bytes_read < 0) {
    if (errno != EAGAIN) {
      RCLCPP_WARN(logger_, "mq_receive failed: %s", strerror(errno));
    }
    return;
  }

  auto * msg = reinterpret_cast<MqMsgPerformanceBridge *>(buffer.data());

  std::string topic_name = msg->target.topic_name;
  topic_local_id_t target_id = msg->target.target_id;
  std::string message_type = msg->message_type;

  RCLCPP_INFO(logger_, "Processing MQ Request: %s (Target ID: %d)", topic_name.c_str(), target_id);

  request_cache_[topic_name][target_id] = *msg;

  RCLCPP_INFO(
    logger_, "Received Request: %s [%s] (Dir: %d)", topic_name.c_str(), message_type.c_str(),
    (int)msg->direction);

  if (!config_handler_->is_topic_allowed(topic_name, msg->direction)) {
    RCLCPP_WARN(logger_, "Request for '%s' denied by filter.", topic_name.c_str());
    return;
  }

  if (msg->direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    if (active_r2a_bridges_.count(topic_name) > 0) {
      RCLCPP_INFO(logger_, "R2A Bridge for '%s' already exists. Skipping.", topic_name.c_str());
      return;
    }

    rclcpp::QoS qos = get_subscriber_qos(topic_name, target_id);
    auto bridge = loader_.create_r2a_bridge(container_node_, topic_name, message_type, qos);

    if (bridge) {
      active_r2a_bridges_[topic_name] = bridge;
      RCLCPP_INFO(logger_, "Activated R2A Bridge. Total active: %zu", active_r2a_bridges_.size());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create R2A Bridge for %s", topic_name.c_str());
    }
  }

  else if (msg->direction == BridgeDirection::AGNOCAST_TO_ROS2) {
    if (active_a2r_bridges_.count(topic_name) > 0) {
      RCLCPP_INFO(logger_, "A2R Bridge for '%s' already exists. Skipping.", topic_name.c_str());
      return;
    }

    rclcpp::QoS qos = get_publisher_qos(topic_name, target_id);
    auto bridge = loader_.create_a2r_bridge(container_node_, topic_name, message_type, qos);

    if (bridge) {
      active_a2r_bridges_[topic_name] = bridge;
      RCLCPP_INFO(logger_, "Activated A2R Bridge. Total active: %zu", active_a2r_bridges_.size());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create A2R Bridge for %s", topic_name.c_str());
    }
  }

  else {
    RCLCPP_ERROR(logger_, "Invalid bridge direction received: %d", (int)msg->direction);
  }
}

void PerformanceBridgeManager::on_signal()
{
  RCLCPP_INFO(logger_, "Shutdown signal received.");
  shutdown_requested_ = true;
  if (executor_) {
    executor_->cancel();
  }
}

void PerformanceBridgeManager::on_reload()
{
  RCLCPP_INFO(logger_, "Reload signal (SIGHUP) received. Reloading config...");

  auto new_config = std::make_unique<BridgeConfigP>(logger_);
  config_handler_ = std::move(new_config);

  if (executor_) {
    executor_->remove_node(container_node_);
  }

  auto cfg = config_handler_->get_current_config();
  RCLCPP_INFO(logger_, "Config reloaded. Mode: %d, Rules: %zu", (int)cfg.mode, cfg.rules.size());

  check_demand_and_recover_bridges();
  check_and_cleanup_bridges();

  if (executor_) {
    executor_->add_node(container_node_);
  }

  RCLCPP_INFO(logger_, "Configuration updated successfully.");
}

void PerformanceBridgeManager::check_and_request_shutdown()
{
  struct ioctl_get_active_process_num_args args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_ACTIVE_PROCESS_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger_, "Failed to get active process count from kernel module.");
    return;
  }

  if (args.ret_active_process_num <= 1) {
    shutdown_requested_ = true;
  }
}

void PerformanceBridgeManager::check_and_remove_bridges()
{
  auto r2a_it = active_r2a_bridges_.begin();
  while (r2a_it != active_r2a_bridges_.end()) {
    const std::string & topic_name = r2a_it->first;

    bool reverse_exists = (active_a2r_bridges_.count(topic_name) > 0);
    int threshold = reverse_exists ? 1 : 0;

    int count = get_agnocast_subscriber_count(topic_name);

    if (count != -1 && count <= threshold) {
      RCLCPP_INFO(logger_, "Removing R2A Bridge: %s", topic_name.c_str());
      r2a_it = active_r2a_bridges_.erase(r2a_it);
    } else {
      ++r2a_it;
    }
  }

  auto a2r_it = active_a2r_bridges_.begin();
  while (a2r_it != active_a2r_bridges_.end()) {
    const std::string & topic_name = a2r_it->first;

    bool reverse_exists = (active_r2a_bridges_.count(topic_name) > 0);
    int threshold = reverse_exists ? 1 : 0;

    int count = get_agnocast_publisher_count(topic_name);

    if (count != -1 && count <= threshold) {
      RCLCPP_INFO(logger_, "Removing A2R Bridge: %s", topic_name.c_str());
      a2r_it = active_a2r_bridges_.erase(a2r_it);
    } else {
      ++a2r_it;
    }
  }
}

void PerformanceBridgeManager::check_demand_and_recover_bridges()
{
  auto config = config_handler_->get_current_config();

  // キャッシュされているトピックごとにループ
  for (auto it = request_cache_.begin(); it != request_cache_.end();) {
    const std::string & topic = it->first;
    auto & id_map = it->second;

    if (id_map.empty()) {
      it = request_cache_.erase(it);
      continue;
    }

    // メッセージ型はトピックで共通のはずなので、代表して1つ取得しておく
    // (もし型すら違うなら、それはシステム設計として異常だが、ここでは先頭を使う)
    std::string message_type = id_map.begin()->second.message_type;

    // ========================================================================
    // 1. R2A (ROS2 -> Agnocast) の復旧試行
    // ========================================================================
    // 条件: 設定で許可されている AND まだブリッジがない
    if (
      config_handler_->is_topic_allowed(topic, BridgeDirection::ROS2_TO_AGNOCAST) &&
      active_r2a_bridges_.count(topic) == 0) {
      // 全体的な需要確認 (Thresholdチェック)
      bool reverse_exists = (active_a2r_bridges_.count(topic) > 0);
      int threshold = reverse_exists ? 1 : 0;
      int count = get_agnocast_subscriber_count(topic);

      if (count != -1 && count > threshold) {
        // IDマップから「R2Aを要求したID」を探して QoS取得を試みる
        for (auto id_it = id_map.begin(); id_it != id_map.end();) {
          topic_local_id_t target_id = id_it->first;
          const auto & req = id_it->second;

          // 方向違いは無視 (A2RのIDを使って SubscriberQoS を取ろうとしない)
          if (req.direction != BridgeDirection::ROS2_TO_AGNOCAST) {
            ++id_it;
            continue;
          }

          try {
            // ★生存確認 & QoS取得 (Subscriber用)
            rclcpp::QoS qos = get_subscriber_qos(topic, target_id);

            RCLCPP_INFO(
              logger_, "[Recovery] Demand found for R2A '%s'. Found valid ID: %d", topic.c_str(),
              target_id);

            auto bridge = loader_.create_r2a_bridge(container_node_, topic, message_type, qos);
            if (bridge) {
              active_r2a_bridges_[topic] = bridge;
              RCLCPP_INFO(logger_, "Activated R2A Bridge (Recovery).");
            }

            // 1つ成功すればこの方向は完了
            break;

          } catch (const std::exception &) {
            // IDが無効なら削除
            id_it = id_map.erase(id_it);
            continue;  // iteratorが進むのでインクリメント不要
          }
          ++id_it;
        }
      }
    }

    // ========================================================================
    // 2. A2R (Agnocast -> ROS2) の復旧試行
    // ========================================================================
    if (
      config_handler_->is_topic_allowed(topic, BridgeDirection::AGNOCAST_TO_ROS2) &&
      active_a2r_bridges_.count(topic) == 0) {
      bool reverse_exists = (active_r2a_bridges_.count(topic) > 0);
      int threshold = reverse_exists ? 1 : 0;
      int count = get_agnocast_publisher_count(topic);

      if (count != -1 && count > threshold) {
        // IDマップから「A2Rを要求したID」を探して QoS取得を試みる
        for (auto id_it = id_map.begin(); id_it != id_map.end();) {
          topic_local_id_t target_id = id_it->first;
          const auto & req = id_it->second;

          // 方向違いは無視
          if (req.direction != BridgeDirection::AGNOCAST_TO_ROS2) {
            ++id_it;
            continue;
          }

          try {
            // ★生存確認 & QoS取得 (Publisher用)
            rclcpp::QoS qos = get_publisher_qos(topic, target_id);

            RCLCPP_INFO(
              logger_, "[Recovery] Demand found for A2R '%s'. Found valid ID: %d", topic.c_str(),
              target_id);

            auto bridge = loader_.create_a2r_bridge(container_node_, topic, message_type, qos);
            if (bridge) {
              active_a2r_bridges_[topic] = bridge;
              RCLCPP_INFO(logger_, "Activated A2R Bridge (Recovery).");
            }
            break;

          } catch (const std::exception &) {
            id_it = id_map.erase(id_it);
            continue;
          }
          ++id_it;
        }
      }
    }

    // ========================================================================
    // 終了処理
    // ========================================================================
    // R2AとA2Rの処理で無効なIDが消された結果、マップが空になった場合のケア
    if (id_map.empty()) {
      it = request_cache_.erase(it);
    } else {
      ++it;
    }
  }
}

void PerformanceBridgeManager::check_and_cleanup_bridges()
{
  RCLCPP_INFO(logger_, "Validating active bridges against new rules...");

  for (auto it = active_r2a_bridges_.begin(); it != active_r2a_bridges_.end();) {
    const std::string & topic = it->first;

    if (!config_handler_->is_topic_allowed(topic, BridgeDirection::ROS2_TO_AGNOCAST)) {
      RCLCPP_WARN(
        logger_, "[Config Change] R2A Bridge for '%s' is no longer allowed. Removing.",
        topic.c_str());

      it = active_r2a_bridges_.erase(it);
    } else {
      ++it;
    }
  }

  for (auto it = active_a2r_bridges_.begin(); it != active_a2r_bridges_.end();) {
    const std::string & topic = it->first;

    if (!config_handler_->is_topic_allowed(topic, BridgeDirection::AGNOCAST_TO_ROS2)) {
      RCLCPP_WARN(
        logger_, "[Config Change] A2R Bridge for '%s' is no longer allowed. Removing.",
        topic.c_str());

      it = active_a2r_bridges_.erase(it);
    } else {
      ++it;
    }
  }
}

// agnocast_bridge_manager_p.cpp

void PerformanceBridgeManager::cleanup_request_cache()
{
  // キャッシュされているトピックごとにループ
  for (auto it = request_cache_.begin(); it != request_cache_.end();) {
    const std::string & topic = it->first;
    auto & id_map = it->second;

    // IDマップ内の各プロセスIDについて生存確認
    for (auto id_it = id_map.begin(); id_it != id_map.end();) {
      topic_local_id_t target_id = id_it->first;
      const auto & req = id_it->second;
      bool is_alive = false;

      try {
        // Agnocast側のIDが生きていれば QoS取得に成功するはず
        if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
          (void)get_subscriber_qos(topic, target_id);
        } else {
          (void)get_publisher_qos(topic, target_id);
        }
        is_alive = true;
      } catch (...) {
        // 例外発生 ＝ プロセス終了 or ID無効
        is_alive = false;
      }

      if (!is_alive) {
        RCLCPP_INFO(
          logger_, "Removed dead ID %d from cache for topic %s", target_id, topic.c_str());
        id_it = id_map.erase(id_it);
      } else {
        ++id_it;
      }
    }

    // IDが空になったトピックはキャッシュ自体から消す
    if (id_map.empty()) {
      it = request_cache_.erase(it);
    } else {
      ++it;
    }
  }
}

}  // namespace agnocast
#include "agnocast/agnocast_bridge_manager_p.hpp"

#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <mqueue.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <unistd.h>

#include <vector>

namespace agnocast
{

PerformanceBridgeManager::PerformanceBridgeManager()
: logger_(rclcpp::get_logger("agnocast_performance_bridge_manager")),
  event_loop_(logger_),
  loader_(logger_),
  config_(logger_)
{
  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  rclcpp::InitOptions init_options{};
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  RCLCPP_INFO(logger_, "Bridge Manager initialized (PID: %d).", getpid());
}

PerformanceBridgeManager::~PerformanceBridgeManager()
{
  if (executor_) {
    executor_->cancel();
  }
  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  executor_.reset();
  container_node_.reset();

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void PerformanceBridgeManager::run()
{
  constexpr int EVENT_LOOP_TIMEOUT_MS = 1000;

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

    check_and_request_shutdown();
  }
}

void PerformanceBridgeManager::start_ros_execution()
{
  std::string node_name = "agnocast_bridge_node_" + std::to_string(getpid());
  container_node_ = std::make_shared<rclcpp::Node>(node_name);

  executor_ = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>();
  executor_->add_node(container_node_);

  executor_thread_ = std::thread([this]() {
    try {
      this->executor_->spin();
    } catch (const std::exception & e) {
      RCLCPP_ERROR(logger_, "Executor Thread CRASHED: %s", e.what());
    }
  });
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
  std::string message_type = msg->message_type;

  // デフォルトQoS設定（Standard版と同じくDepth 10など）
  rclcpp::QoS default_qos(10);

  RCLCPP_INFO(
    logger_, "Received Request: %s [%s] (Dir: %d)", topic_name.c_str(), message_type.c_str(),
    (int)msg->direction);

  // ---------------------------------------------------------
  // R2A: ROS 2 -> Agnocast
  // ---------------------------------------------------------
  if (msg->direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    // ★修正: 構造体のメンバ変数 topic_name を参照
    for (const auto & bridge_entry : active_r2a_bridges_) {
      if (bridge_entry.topic_name == topic_name) {
        RCLCPP_DEBUG(logger_, "R2A Bridge for '%s' already exists. Skipping.", topic_name.c_str());
        return;
      }
    }

    auto bridge = loader_.create_r2a_bridge(container_node_, topic_name, message_type, default_qos);

    if (bridge) {
      // ★修正: 構造体を作って保存 {トピック名, ポインタ}
      active_r2a_bridges_.push_back({topic_name, bridge});
      RCLCPP_INFO(logger_, "Activated R2A Bridge. Total active: %zu", active_r2a_bridges_.size());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create R2A Bridge for %s", topic_name.c_str());
    }
  }
  // ---------------------------------------------------------
  // A2R: Agnocast -> ROS 2
  // ---------------------------------------------------------
  else if (msg->direction == BridgeDirection::AGNOCAST_TO_ROS2) {
    // ★修正: 構造体のメンバ変数 topic_name を参照
    for (const auto & bridge_entry : active_a2r_bridges_) {
      if (bridge_entry.topic_name == topic_name) {
        RCLCPP_DEBUG(logger_, "A2R Bridge for '%s' already exists. Skipping.", topic_name.c_str());
        return;
      }
    }

    auto bridge = loader_.create_a2r_bridge(container_node_, topic_name, message_type, default_qos);

    if (bridge) {
      // ★修正: 構造体を作って保存 {トピック名, ポインタ}
      active_a2r_bridges_.push_back({topic_name, bridge});
      RCLCPP_INFO(logger_, "Activated A2R Bridge. Total active: %zu", active_a2r_bridges_.size());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create A2R Bridge for %s", topic_name.c_str());
    }
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
  RCLCPP_INFO(logger_, "Reload signal (SIGHUP) received.");
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

}  // namespace agnocast
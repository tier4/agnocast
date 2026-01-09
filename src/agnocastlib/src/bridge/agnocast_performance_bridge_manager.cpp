
#include "agnocast/bridge/agnocast_performance_bridge_manager.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "agnocast/agnocast_utils.hpp"
#include "agnocast/bridge/agnocast_bridge_utils.hpp"

#include <mqueue.h>
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

  RCLCPP_INFO(logger_, "Performance Bridge Manager initialized (PID: %d).", getpid());
}

PerformanceBridgeManager::~PerformanceBridgeManager()
{
  if (executor_) {
    executor_->cancel();
  }

  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void PerformanceBridgeManager::run()
{
  constexpr int EVENT_LOOP_TIMEOUT_MS = 1000;
  constexpr int MAINTENANCE_INTERVAL = 10;
  int maintenance_counter = 0;

  std::string proc_name = "agno_pbr_" + std::to_string(getpid());
  prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0);

  // TODO(yutarokobayashi): For debugging. Remove later.
  RCLCPP_INFO(logger_, "Performance Bridge Manager started.");

  start_ros_execution();

  event_loop_.set_mq_handler([this](int fd) { this->on_mq_request(fd); });
  event_loop_.set_signal_handler([this]() { this->on_signal(); });
  event_loop_.set_reload_handler([this]() { this->on_reload(); });

  while (!shutdown_requested_) {
    if (!event_loop_.spin_once(EVENT_LOOP_TIMEOUT_MS)) {
      RCLCPP_ERROR(logger_, "Event loop spin failed.");
      break;
    }

    if (config_.get_current_config().mode == FilterMode::ALLOW_ALL) {
      poll_ros2_demand_and_create_bridges();
    }

    if (++maintenance_counter >= MAINTENANCE_INTERVAL) {
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

  // TODO(yutarokobayashi): Select executor type based on config
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

  ssize_t bytes_read = mq_receive(fd, buffer.data(), buffer.size(), nullptr);

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

  // TODO(yutarokobayashi): For debugging. Remove later.
  RCLCPP_INFO(logger_, "Processing MQ Request: %s (Target ID: %d)", topic_name.c_str(), target_id);

  if (!config_.is_topic_allowed(topic_name, msg->direction)) {
    // TODO(yutarokobayashi): For debugging. Remove later.
    RCLCPP_WARN(logger_, "Request for '%s' denied by filter.", topic_name.c_str());
    return;
  }

  request_cache_[topic_name][target_id] = *msg;

  if (msg->direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    if (active_r2a_bridges_.count(topic_name) > 0) {
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "R2A Bridge for '%s' already exists. Skipping.", topic_name.c_str());
      return;
    }

    rclcpp::QoS qos = get_subscriber_qos(topic_name, target_id);
    auto bridge = loader_.create_r2a_bridge(container_node_, topic_name, message_type, qos);

    if (bridge) {
      active_r2a_bridges_[topic_name] = bridge;
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Activated R2A Bridge. Total active: %zu", active_r2a_bridges_.size());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create R2A Bridge for %s", topic_name.c_str());
    }
  } else if (msg->direction == BridgeDirection::AGNOCAST_TO_ROS2) {
    if (active_a2r_bridges_.count(topic_name) > 0) {
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "A2R Bridge for '%s' already exists. Skipping.", topic_name.c_str());
      return;
    }

    rclcpp::QoS qos = get_publisher_qos(topic_name, target_id);
    auto bridge = loader_.create_a2r_bridge(container_node_, topic_name, message_type, qos);

    if (bridge) {
      active_a2r_bridges_[topic_name] = bridge;
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Activated A2R Bridge. Total active: %zu", active_a2r_bridges_.size());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create A2R Bridge for %s", topic_name.c_str());
    }
  } else {
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
  // TODO(yutarokobayashi): Implement configuration reload
  RCLCPP_INFO(logger_, "Reload signal (SIGHUP) received.");
}

topic_local_id_t PerformanceBridgeManager::find_candidate_id(
  const RequestMap & id_map, BridgeDirection direction) const
{
  topic_local_id_t max_id = -1;
  bool found = false;

  for (const auto & [id, req] : id_map) {
    if (req.direction == direction) {
      if (!found || id > (topic_local_id_t)max_id) {
        max_id = id;
        found = true;
      }
    }
  }
  return found ? max_id : -1;
}

void PerformanceBridgeManager::attempt_create_r2a(
  const std::string & topic, RequestMap & id_map, const std::string & message_type)
{
  if (active_r2a_bridges_.count(topic) > 0) return;

  bool reverse_exists = (active_a2r_bridges_.count(topic) > 0);
  int threshold = reverse_exists ? 1 : 0;
  int count = get_agnocast_subscriber_count(topic);

  if (count == -1 || count <= threshold) return;

  if (!has_external_ros2_publisher(container_node_.get(), topic)) return;

  topic_local_id_t max_id = find_candidate_id(id_map, BridgeDirection::ROS2_TO_AGNOCAST);
  if (max_id == -1) return;

  try {
    rclcpp::QoS qos = get_subscriber_qos(topic, max_id);
    RCLCPP_INFO(logger_, "[Poll] Creating R2A '%s' (ROS2 Pub Detected).", topic.c_str());

    auto bridge = loader_.create_r2a_bridge(container_node_, topic, message_type, qos);
    if (bridge) active_r2a_bridges_[topic] = bridge;
  } catch (const std::exception & e) {
    RCLCPP_WARN(
      logger_, "Failed to create R2A bridge for '%s': %s. Removing request ID %d.", topic.c_str(),
      e.what(), max_id);
    id_map.erase(max_id);
  } catch (...) {
    id_map.erase(max_id);
  }
}

void PerformanceBridgeManager::attempt_create_a2r(
  const std::string & topic, RequestMap & id_map, const std::string & message_type)
{
  if (active_a2r_bridges_.count(topic) > 0) return;

  bool reverse_exists = (active_r2a_bridges_.count(topic) > 0);
  int threshold = reverse_exists ? 1 : 0;
  int count = get_agnocast_publisher_count(topic);

  if (count == -1 || count <= threshold) return;

  if (!agnocast::has_external_ros2_subscriber(container_node_.get(), topic)) return;

  topic_local_id_t max_id = find_candidate_id(id_map, BridgeDirection::AGNOCAST_TO_ROS2);
  if (max_id == -1) return;

  try {
    rclcpp::QoS qos = get_publisher_qos(topic, max_id);
    RCLCPP_INFO(logger_, "[Poll] Creating A2R '%s' (ROS2 Sub Detected).", topic.c_str());

    auto bridge = loader_.create_a2r_bridge(container_node_, topic, message_type, qos);
    if (bridge) active_a2r_bridges_[topic] = bridge;
  } catch (const std::exception & e) {
    RCLCPP_WARN(
      logger_, "Failed to create A2R bridge for '%s': %s. Removing request ID %d.", topic.c_str(),
      e.what(), max_id);
    id_map.erase(max_id);
  } catch (...) {
    id_map.erase(max_id);
  }
}

void PerformanceBridgeManager::poll_ros2_demand_and_create_bridges()
{
  for (auto it = request_cache_.begin(); it != request_cache_.end();) {
    const std::string & topic = it->first;
    auto & id_map = it->second;

    if (id_map.empty()) {
      it = request_cache_.erase(it);
      continue;
    }

    std::string message_type = id_map.begin()->second.message_type;

    attempt_create_r2a(topic, id_map, message_type);
    attempt_create_a2r(topic, id_map, message_type);

    if (id_map.empty()) {
      it = request_cache_.erase(it);
    } else {
      ++it;
    }
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
      // TODO(yutarokobayashi): For debugging. Remove later.
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
      // TODO(yutarokobayashi): For debugging. Remove later.
      RCLCPP_INFO(logger_, "Removing A2R Bridge: %s", topic_name.c_str());
      a2r_it = active_a2r_bridges_.erase(a2r_it);
    } else {
      ++a2r_it;
    }
  }
}

void PerformanceBridgeManager::check_and_request_shutdown()
{
  struct ioctl_get_process_num_args args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_PROCESS_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger_, "Failed to get active process count from kernel module.");
    return;
  }

  // Request shutdown if there is no other process excluding poll_for_unlink.
  if (args.ret_process_num <= 1) {
    shutdown_requested_ = true;
  }
}

void PerformanceBridgeManager::cleanup_request_cache()
{
  for (auto it = request_cache_.begin(); it != request_cache_.end();) {
    const std::string & topic = it->first;
    auto & id_map = it->second;

    for (auto id_it = id_map.begin(); id_it != id_map.end();) {
      topic_local_id_t target_id = id_it->first;
      const auto & req = id_it->second;
      bool is_alive = false;

      try {
        if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
          (void)get_subscriber_qos(topic, target_id);
        } else {
          (void)get_publisher_qos(topic, target_id);
        }
        is_alive = true;
      } catch (...) {
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

    if (id_map.empty()) {
      it = request_cache_.erase(it);
    } else {
      ++it;
    }
  }
}

}  // namespace agnocast

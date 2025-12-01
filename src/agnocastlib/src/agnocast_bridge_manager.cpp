#include "agnocast/agnocast_bridge_manager.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <signal.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <unistd.h>

#include <chrono>
#include <cstring>
#include <stdexcept>

extern "C" bool agnocast_heaphook_init_daemon();

namespace agnocast
{

BridgeManager::BridgeManager(pid_t target_pid)
: target_pid_(target_pid),
  logger_(rclcpp::get_logger("agnocast_bridge_manager")),
  event_loop_(target_pid, logger_),
  loader_(logger_)
{
  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
  rclcpp::InitOptions init_options;
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  if (!agnocast_heaphook_init_daemon()) {
    RCLCPP_ERROR(logger_, "Heaphook init FAILED.");
  }
}

BridgeManager::~BridgeManager()
{
  if (executor_) {
    executor_->cancel();
  }
  if (executor_thread_.joinable()) {
    executor_thread_.join();
  }

  RCLCPP_INFO(logger_, "Agnocast Bridge Manager shutting down.");

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }
}

void BridgeManager::run()
{
  std::string proc_name = "agno_br_" + std::to_string(getpid());
  prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0);

  setup_ros_execution();

  event_loop_.set_parent_mq_handler([this](int fd) { this->on_mq_event(fd, true); });
  event_loop_.set_child_mq_handler([this](int fd) { this->on_mq_event(fd, false); });
  event_loop_.set_signal_handler([this]() { this->on_signal(); });

  auto last_gc_time = std::chrono::steady_clock::now();
  constexpr auto GC_INTERVAL = std::chrono::seconds(1);

  while (!shutdown_requested_ && rclcpp::ok()) {
    check_parent_alive();

    auto now = std::chrono::steady_clock::now();
    if (now - last_gc_time >= GC_INTERVAL) {
      check_connection_demand();
      last_gc_time = now;
      check_should_exit();
    }

    if (shutdown_requested_) break;

    event_loop_.spin_once(1000);
  }
}

void BridgeManager::setup_ros_execution()
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
    }
  });
}

void BridgeManager::on_mq_event(mqd_t fd, bool allow_delegation)
{
  MqMsgBridge req;
  while (mq_receive(fd, (char *)&req, sizeof(req), nullptr) > 0) {
    handle_create_request(req, allow_delegation);
  }
}

void BridgeManager::on_signal()
{
  RCLCPP_INFO(logger_, "Signal received. Shutting down.");
  shutdown_requested_ = true;
  if (executor_) {
    executor_->cancel();
  }
}

void BridgeManager::handle_create_request(const MqMsgBridge & req, bool allow_delegation)
{
  std::string unique_key = generate_unique_key(req);
  std::string topic_name = req.target.topic_name;

  std::lock_guard<std::mutex> lock(executor_mutex_);

  if (active_bridges_.count(unique_key)) return;

  struct ioctl_bridge_args args;
  std::memset(&args, 0, sizeof(args));
  args.pid = getpid();
  snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", topic_name.c_str());

  if (ioctl(agnocast_fd, AGNOCAST_REGISTER_BRIDGE_CMD, &args) == 0) {
    auto bridge = loader_.load_and_create(req, unique_key, container_node_);
    if (bridge) {
      active_bridges_[unique_key] = bridge;
      RCLCPP_INFO(logger_, "Registered owner for '%s'", unique_key.c_str());
    } else {
      RCLCPP_ERROR(logger_, "Failed to create bridge for '%s'", unique_key.c_str());
      unregister_from_kernel(topic_name);
    }

  } else if (errno == EEXIST) {
    if (allow_delegation) {
      union ioctl_get_bridge_pid_args bridge_args;
      std::memset(&bridge_args, 0, sizeof(bridge_args));
      snprintf(bridge_args.topic_name, MAX_TOPIC_NAME_LEN, "%s", topic_name.c_str());

      if (ioctl(agnocast_fd, AGNOCAST_GET_BRIDGE_PID_CMD, &bridge_args) == 0) {
        pid_t owner_pid = bridge_args.ret_pid;
        send_delegate_request(owner_pid, req);
        RCLCPP_INFO(logger_, "Delegated '%s' to PID %d", unique_key.c_str(), owner_pid);
      }
    } else {
      RCLCPP_WARN(
        logger_, "Delegate failed (EEXIST) for '%s'. Another owner exists. Stop.",
        unique_key.c_str());
    }
  }
}

void BridgeManager::remove_bridge_node_locked(const std::string & unique_key)
{
  if (!active_bridges_.count(unique_key)) return;

  active_bridges_.erase(unique_key);
  RCLCPP_INFO(logger_, "Removed bridge entry: %s", unique_key.c_str());

  if (unique_key.size() > 4) {
    std::string topic_name = unique_key.substr(0, unique_key.length() - 4);
    bool is_r2a = (unique_key.find("_R2A") != std::string::npos);
    std::string reverse_key = topic_name + (is_r2a ? "_A2R" : "_R2A");

    if (active_bridges_.count(reverse_key) == 0) {
      unregister_from_kernel(topic_name);
    }
  }

  check_should_exit();
}

void BridgeManager::check_connection_demand()
{
  std::vector<std::string> to_remove;
  std::lock_guard<std::mutex> lock(executor_mutex_);

  for (auto & [key, bridge] : active_bridges_) {
    if (key.size() <= 4) continue;
    std::string topic_name = key.substr(0, key.length() - 4);
    bool is_r2a = (key.find("_R2A") != std::string::npos);

    std::string reverse_key = topic_name + (is_r2a ? "_A2R" : "_R2A");
    int threshold = (active_bridges_.count(reverse_key) > 0) ? 1 : 0;

    int count = get_agnocast_connection_count(topic_name, is_r2a);
    if (count >= 0 && count <= threshold) {
      RCLCPP_INFO(
        logger_, "Bridge '%s' unused (Count:%d). Queued for removal.", key.c_str(), count);
      to_remove.push_back(key);
    }
  }

  for (const auto & key : to_remove) {
    remove_bridge_node_locked(key);
  }
}

void BridgeManager::check_should_exit()
{
  if (!is_parent_alive_ && active_bridges_.empty()) {
    RCLCPP_INFO(logger_, "Shutdown condition met.");
    shutdown_requested_ = true;
    if (executor_) executor_->cancel();
  }
}

void BridgeManager::check_parent_alive()
{
  if (!is_parent_alive_) return;
  if (kill(target_pid_, 0) != 0) {
    RCLCPP_INFO(logger_, "Parent exited. Detaching.");
    is_parent_alive_ = false;
    event_loop_.close_parent_mq();
    check_should_exit();
  }
}

std::string BridgeManager::generate_unique_key(const MqMsgBridge & req)
{
  return std::string(req.target.topic_name) +
         ((req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_R2A" : "_A2R");
}

int BridgeManager::get_agnocast_connection_count(const std::string & topic_name, bool is_r2a)
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
  return (ret == 0) ? static_cast<int>(count) : -1;
}

void BridgeManager::unregister_from_kernel(const std::string & topic_name)
{
  struct ioctl_bridge_args args;
  std::memset(&args, 0, sizeof(args));
  args.pid = getpid();
  snprintf(args.topic_name, MAX_TOPIC_NAME_LEN, "%s", topic_name.c_str());
  if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &args) == 0) {
    RCLCPP_INFO(logger_, "Unregistered bridge owner for '%s'", topic_name.c_str());
  }
}

void BridgeManager::send_delegate_request(pid_t target_pid, const MqMsgBridge & req)
{
  std::string mq_name = create_mq_name_for_bridge_child(target_pid);
  mqd_t mq = mq_open(mq_name.c_str(), O_WRONLY | O_CLOEXEC);
  if (mq != (mqd_t)-1) {
    mq_send(mq, reinterpret_cast<const char *>(&req), sizeof(req), 0);
    mq_close(mq);
  } else {
    RCLCPP_WARN(logger_, "Failed to delegate to PID %d", target_pid);
  }
}

}  // namespace agnocast

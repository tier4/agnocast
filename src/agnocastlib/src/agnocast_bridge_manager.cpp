#include "agnocast/agnocast_bridge_manager.hpp"

#include <sys/prctl.h>
#include <unistd.h>

#include <csignal>
#include <stdexcept>
#include <string>

namespace agnocast
{

BridgeManager::BridgeManager(pid_t target_pid)
: target_pid_(target_pid),
  logger_(rclcpp::get_logger("agnocast_bridge_manager")),
  event_loop_(target_pid, logger_),
  loader_(logger_)
{
  // Optimization: Fail-fast to avoid rclcpp::init overhead.
  // Note that the process ensures correct termination even without this check.
  if (kill(target_pid_, 0) != 0) {
    throw std::runtime_error("Target parent process is already dead.");
  }

  if (rclcpp::ok()) {
    rclcpp::shutdown();
  }

  rclcpp::InitOptions init_options{};
  init_options.shutdown_on_signal = false;
  rclcpp::init(0, nullptr, init_options);

  // TODO(yutarokobayashi): heaphook init
}

BridgeManager::~BridgeManager()
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

void BridgeManager::run()
{
  constexpr int EVENT_LOOP_TIMEOUT_MS = 1000;

  std::string proc_name = "agno_br_" + std::to_string(getpid());
  prctl(PR_SET_NAME, proc_name.c_str(), 0, 0, 0);

  start_ros_execution();

  event_loop_.set_parent_mq_handler([this](int fd) { this->on_mq_event(fd, true); });
  event_loop_.set_signal_handler([this]() { this->on_signal(); });

  while (!shutdown_requested_) {
    check_parent_alive();
    check_active_bridges();
    check_should_exit();

    if (shutdown_requested_) {
      break;
    }

    if (!event_loop_.spin_once(EVENT_LOOP_TIMEOUT_MS)) {
      break;
    }
  }
}

void BridgeManager::start_ros_execution()
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

void BridgeManager::on_mq_event(mqd_t fd, bool allow_delegation)
{
  MqMsgBridge req{};
  while (mq_receive(fd, reinterpret_cast<char *>(&req), sizeof(req), nullptr) > 0) {
    handle_create_request(req, allow_delegation);
  }
}

void BridgeManager::on_signal()
{
  shutdown_requested_ = true;
  if (executor_) {
    executor_->cancel();
  }
}

void BridgeManager::handle_create_request(const MqMsgBridge & req, bool /*allow_delegation*/)
{
  // The 'allow_delegation' flag indicates the source of the request:
  // - true: Initial request from the parent process. Delegation to an existing owner is allowed.
  // - false: Request received from a peer child process (already delegated). Further delegation
  //          is disabled to prevent infinite loops.
  // Note: This check (if false) acts as a safety guard against unexpected infinite recursion loops
  // due to race conditions or timing issues. It is not expected to be triggered in normal
  // operation.

  // Locally, unique keys include the direction. However, we register the raw topic name (without
  // direction) to the kernel to enforce single-process ownership for the entire topic.
  std::string topic_name(
    &req.target.topic_name[0], strnlen(&req.target.topic_name[0], sizeof(req.target.topic_name)));
  std::string topic_name_with_direction =
    topic_name + ((req.direction == BridgeDirection::ROS2_TO_AGNOCAST) ? "_R2A" : "_A2R");

  if (active_bridges_.count(topic_name_with_direction) != 0U) {
    return;
  }

  // TODO(yutarokobayashi): The following comments are scheduled for implementation in a later PR.
  struct ioctl_add_bridge_args add_bridge_args
  {
  };
  std::memset(&add_bridge_args, 0, sizeof(add_bridge_args));
  add_bridge_args.pid = getpid();
  add_bridge_args.topic_name = {topic_name.c_str(), topic_name.size()};

  if (ioctl(agnocast_fd, AGNOCAST_ADD_BRIDGE_CMD, &add_bridge_args) == 0) {
    // Registration successful: Load and create the bridge instance
    // Rollback kernel registration if bridge creation fails
  } else if (errno == EEXIST) {
    [[maybe_unused]] pid_t owner_pid = add_bridge_args.ret_pid;
    // The bridge is already registered in the kernel (EEXIST case)
    // If allow_delegation is true, retrieve the PID of the current owner and delegate.
    // Otherwise, abort to avoid loops.
  } else {
    RCLCPP_ERROR(logger, "AGNOCAST_ADD_BRIDGE_CMD failed: %s", strerror(errno));
  }
}

void BridgeManager::check_parent_alive()
{
  if (!is_parent_alive_) {
    return;
  }
  if (kill(target_pid_, 0) != 0) {
    is_parent_alive_ = false;
    event_loop_.close_parent_mq();
  }
}

void BridgeManager::check_active_bridges()
{
  // TODO(yutarokobayashi): Verifying the number of connections and get remove bridge name
  remove_active_bridges("TOPIC_R2A");
}

// TODO(yutarokobayashi): Reconsider the exit logic.
// This implementation should be revisited and finalized after fully understanding the overall
// shutdown sequence.
void BridgeManager::check_should_exit()
{
  if (!is_parent_alive_ && active_bridges_.empty()) {
    shutdown_requested_ = true;
    if (executor_) {
      executor_->cancel();
    }
  }
}

void BridgeManager::remove_active_bridges(const std::string & topic_name_with_dirction)
{
  if (active_bridges_.count(topic_name_with_dirction) == 0) {
    return;
  }

  active_bridges_.erase(topic_name_with_dirction);
  // TODO(yutarokobayashi): Unregister from the kernel only if the paired bridge in the reverse
  // direction is also missing.
}

}  // namespace agnocast

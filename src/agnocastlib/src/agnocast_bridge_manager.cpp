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

  event_loop_.set_parent_mq_handler([this](int fd) { this->on_mq_create_request(fd); });
  event_loop_.set_peer_mq_handler([this](int fd) { this->on_mq_delegation_request(fd); });
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

void BridgeManager::on_mq_create_request(mqd_t fd)
{
  MqMsgBridge req{};
  while (mq_receive(fd, reinterpret_cast<char *>(&req), sizeof(req), nullptr) > 0) {
    handle_create_request(req);
  }
}

void BridgeManager::on_mq_delegation_request(mqd_t fd)
{
  MqMsgBridge req{};
  while (mq_receive(fd, reinterpret_cast<char *>(&req), sizeof(req), nullptr) > 0) {
    handle_delegate_request(req);
  }
}

void BridgeManager::on_signal()
{
  shutdown_requested_ = true;
  if (executor_) {
    executor_->cancel();
  }
}

void BridgeManager::handle_create_request(const MqMsgBridge & req)
{
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
    auto bridge = loader_.create(req, topic_name_with_direction, container_node_);
    if (bridge) {
      active_bridges_[topic_name_with_direction] = bridge;
    } else {
      RCLCPP_ERROR(logger_, "Failed to create bridge for '%s'", topic_name_with_direction.c_str());
      // Rollback kernel registration.
    }
  } else if (errno == EEXIST) {
    [[maybe_unused]] pid_t owner_pid = add_bridge_args.ret_pid;
    // The bridge is already registered in the kernel (EEXIST case)
    // Retrieve the PID of the current owner and delegate.
  } else {
    RCLCPP_ERROR(logger, "AGNOCAST_ADD_BRIDGE_CMD failed: %s", strerror(errno));
  }
}

void BridgeManager::handle_delegate_request(const MqMsgBridge & /*req*/)
{
  // TODO(yutarokobayashi): I plan to implement the logic for when delegation occurs in a later PR.
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
  constexpr std::string_view SUFFIX_R2A = "_R2A";
  constexpr std::string_view SUFFIX_A2R = "_A2R";
  constexpr size_t SUFFIX_LEN = 4;  // "_R2A" or "_A2R" length

  std::vector<std::string> to_remove;
  to_remove.reserve(active_bridges_.size());

  for (const auto & [key, bridge] : active_bridges_) {
    if (key.size() <= SUFFIX_LEN) {
      continue;
    }

    std::string_view key_view = key;
    std::string_view suffix = key_view.substr(key_view.size() - SUFFIX_LEN);
    std::string_view topic_name_view = key_view.substr(0, key_view.size() - SUFFIX_LEN);

    bool is_r2a = (suffix == SUFFIX_R2A);
    std::string reverse_key(topic_name_view);
    reverse_key += (is_r2a ? SUFFIX_A2R : SUFFIX_R2A);

    // If the reverse bridge exists locally, it holds one internal Agnocast Pub/Sub instance.
    // We set the threshold to 1 to exclude this self-count and detect only external demand.
    const bool reverse_exists = (active_bridges_.count(reverse_key) > 0);
    const int threshold = reverse_exists ? 1 : 0;

    int count = get_agnocast_connection_count(std::string(topic_name_view), is_r2a);

    if (count <= threshold) {
      if (count < 0) {
        RCLCPP_ERROR(
          logger_, "Failed to get connection count for %s. Removing bridge.", key.c_str());
      }
      to_remove.push_back(key);
    }
  }

  for (const auto & key : to_remove) {
    remove_active_bridges(key);
  }
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

int BridgeManager::get_agnocast_connection_count(const std::string & topic_name, bool is_r2a)
{
  uint32_t count = 0;

  if (is_r2a) {
    union ioctl_get_subscriber_num_args get_subscriber_count_args = {};
    get_subscriber_count_args.topic_name = {topic_name.c_str(), topic_name.size()};
    if (ioctl(agnocast_fd, AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_GET_SUBSCRIBER_NUM_CMD failed: %s", strerror(errno));
      return -1;
    }
    count = get_subscriber_count_args.ret_subscriber_num;
  } else {
    union ioctl_get_publisher_num_args get_publisher_count_args = {};
    get_publisher_count_args.topic_name = {topic_name.c_str(), topic_name.size()};
    if (ioctl(agnocast_fd, AGNOCAST_GET_PUBLISHER_NUM_CMD, &get_publisher_count_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_GET_PUBLISHER_NUM_CMD failed: %s", strerror(errno));
      return -1;
    }
    count = get_publisher_count_args.ret_publisher_num;
  }
  return static_cast<int>(count);
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

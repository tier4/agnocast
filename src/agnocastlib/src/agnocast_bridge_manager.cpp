#include "agnocast/agnocast_bridge_manager.hpp"

#include "agnocast/agnocast_bridge_plugin_api.hpp"
#include "agnocast/agnocast_callback_isolated_executor.hpp"
#include "agnocast/agnocast_multi_threaded_executor.hpp"
#include "agnocast/agnocast_single_threaded_executor.hpp"

#include <dlfcn.h>
#include <signal.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <yaml-cpp/yaml.h>

#include <cerrno>
#include <cstring>

constexpr long MAX_MSG = 10;
constexpr int MAX_EVENTS = 10;
constexpr int WHILE_POLL_DELAY_MS = 1000;

namespace agnocast
{
std::atomic<bool> BridgeManager::reload_filter_request_(false);

BridgeManager::BridgeManager()
: bridge_config_(parse_bridge_config()),
  node_(std::make_shared<rclcpp::Node>("agnocast_bridge_manager")),
  logger_(node_->get_logger()),
  executor_(select_executor()),
  mq_((mqd_t)-1),
  epoll_fd_(-1),
  mq_name_str_(create_mq_name_for_bridge())
{
  try {
    setup_message_queue();
    setup_signal_handler();
    setup_epoll();
    start_executor_thread();

    RCLCPP_INFO(logger_, "[BRIDGE MANAGER DAEMON] PID: %d", getpid());
  } catch (const std::exception & e) {
    RCLCPP_ERROR(logger_, "BridgeManager initialization failed: %s", e.what());
    throw;
  }
}

BridgeManager::~BridgeManager()
{
  if (executor_) {
    executor_->cancel();
  }
  if (spin_thread_.joinable()) {
    spin_thread_.join();
  }

  if (epoll_fd_ != -1) {
    close(epoll_fd_);
    epoll_fd_ = -1;
  }

  if (mq_ != (mqd_t)-1) {
    mq_close(mq_);
    mq_ = (mqd_t)-1;
  }

  if (!mq_name_str_.empty()) {
    mq_unlink(mq_name_str_.c_str());
  }
}

void BridgeManager::run()
{
  struct epoll_event events[MAX_EVENTS];

  while (rclcpp::ok()) {
    int num_events = epoll_wait(epoll_fd_, events, MAX_EVENTS, WHILE_POLL_DELAY_MS);

    if (num_events < 0) {
      if (errno == EINTR) continue;
      RCLCPP_ERROR(logger_, "epoll_wait() failed: %s", strerror(errno));
      break;
    }

    if (reload_filter_request_.load()) {
      reload_filter_request_.store(false);
      reload_and_update_bridges();
    }

    if (num_events == 0) {
      check_and_shutdown_idle_bridges();
      check_and_shutdown_daemon_if_idle();
    }

    for (int i = 0; i < num_events; i++) {
      if (events[i].data.fd == mq_) {
        check_and_shutdown_idle_bridges();
        handle_bridge_request();
      }
    }
  }

  shutdown_manager_internal();
}

void BridgeManager::setup_message_queue()
{
  const char * mq_name = mq_name_str_.c_str();
  struct mq_attr attr{};
  attr.mq_maxmsg = MAX_MSG;
  attr.mq_msgsize = sizeof(BridgeRequest);

  mq_unlink(mq_name);

  mq_ = mq_open(mq_name, O_CREAT | O_RDONLY, 0644, &attr);
  if (mq_ == (mqd_t)-1) {
    RCLCPP_ERROR(logger_, "mq_open failed: %s", strerror(errno));
    throw std::runtime_error("Failed to open message queue");
  }
}

void BridgeManager::setup_signal_handler()
{
  struct sigaction sa{};
  sa.sa_handler = BridgeManager::sighup_handler;
  sigemptyset(&sa.sa_mask);

  if (sigaction(SIGHUP, &sa, NULL) == -1) {
    RCLCPP_ERROR(logger_, "sigaction(SIGHUP) failed: %s", strerror(errno));
    throw std::runtime_error("Failed to set SIGHUP handler");
  }
}

void BridgeManager::setup_epoll()
{
  epoll_fd_ = epoll_create1(0);
  if (epoll_fd_ == -1) {
    RCLCPP_ERROR(logger_, "epoll_create1 failed: %s", strerror(errno));
    throw std::runtime_error("epoll_create1 failed");
  }

  struct epoll_event ev{};
  ev.events = EPOLLIN;
  ev.data.fd = mq_;

  if (epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, mq_, &ev) == -1) {
    RCLCPP_ERROR(logger_, "epoll_ctl failed to add mq: %s", strerror(errno));
    close(epoll_fd_);
    epoll_fd_ = -1;
    throw std::runtime_error("epoll_ctl failed");
  }
}

void BridgeManager::start_executor_thread()
{
  executor_->add_node(node_);
  spin_thread_ = std::thread([this]() { this->executor_->spin(); });
}

void BridgeManager::launch_r2a_bridge_thread(const BridgeRequest & request)
{
  load_and_launch_plugin<ActiveBridgeR2A, CreateR2ABridgeFunc, rclcpp::SubscriptionBase::SharedPtr>(
    request, this->active_r2a_bridges_, "r2a", "create_r2a_bridge");
}

void BridgeManager::launch_a2r_bridge_thread(const BridgeRequest & request)
{
  load_and_launch_plugin<
    ActiveBridgeA2R, CreateA2RBridgeFunc, std::shared_ptr<agnocast::SubscriptionBase> >(
    request, this->active_a2r_bridges_, "a2r", "create_a2r_bridge");
}

bool BridgeManager::is_request_allowed(const BridgeRequest & req) const
{
  auto rule_matches = [&](const BridgeConfigEntry & entry) {
    return entry.topic_name == std::string(req.topic_name) &&
           entry.message_type == std::string(req.message_type) &&
           (entry.direction == req.direction || entry.direction == BridgeDirection::BIDIRECTIONAL);
  };

  switch (bridge_config_.mode) {
    case FilterMode::ALLOW_ALL:
      return true;
    case FilterMode::WHITELIST:
      return std::any_of(bridge_config_.rules.begin(), bridge_config_.rules.end(), rule_matches);
    case FilterMode::BLACKLIST:
      return !std::any_of(bridge_config_.rules.begin(), bridge_config_.rules.end(), rule_matches);
  }

  return false;
}

bool BridgeManager::does_bridge_exist(const BridgeRequest & req) const
{
  auto topic_matches = [&](const auto & bridge) {
    return bridge.topic_name == std::string(req.topic_name);
  };

  if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    return std::any_of(active_r2a_bridges_.begin(), active_r2a_bridges_.end(), topic_matches);
  } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
    return std::any_of(active_a2r_bridges_.begin(), active_a2r_bridges_.end(), topic_matches);
  }
  return false;
}

void BridgeManager::handle_bridge_request()
{
  BridgeRequest req;
  if (mq_receive(mq_, (char *)&req, sizeof(BridgeRequest), NULL) < 0) {
    return;
  }

  if (!is_request_allowed(req)) {
    RCLCPP_DEBUG(logger_, "Bridge request rejected by filter: %s", req.topic_name);
    return;
  }

  {
    std::lock_guard<std::mutex> lock(bridge_mutex_);
    if (does_bridge_exist(req)) {
      RCLCPP_DEBUG(logger_, "Bridge request ignored (already exists): %s", req.topic_name);
      return;
    }
  }

  if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
    worker_threads_.emplace_back(&BridgeManager::launch_r2a_bridge_thread, this, req);
  } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
    worker_threads_.emplace_back(&BridgeManager::launch_a2r_bridge_thread, this, req);
  }
}

void BridgeManager::calculate_bridge_diff(
  const BridgeConfig & new_config, std::vector<BridgeConfigEntry> & to_add,
  std::vector<ActiveBridgeR2A> & to_remove_r2a, std::vector<ActiveBridgeA2R> & to_remove_a2r)
{
  std::lock_guard<std::mutex> lock(bridge_mutex_);

  auto is_r2a_allowed = [&](const ActiveBridgeR2A & bridges) {
    if (new_config.mode == FilterMode::ALLOW_ALL) return true;
    bool found = false;
    for (const auto & entry : new_config.rules) {
      if (
        entry.topic_name == bridges.topic_name &&
        (entry.direction == BridgeDirection::ROS2_TO_AGNOCAST ||
         entry.direction == BridgeDirection::BIDIRECTIONAL)) {
        found = true;
        break;
      }
    }
    return (new_config.mode == FilterMode::WHITELIST) ? found : !found;
  };
  active_r2a_bridges_.erase(
    std::remove_if(
      active_r2a_bridges_.begin(), active_r2a_bridges_.end(),
      [&](const ActiveBridgeR2A & bridge) {
        if (is_r2a_allowed(bridge)) {
          return false;
        }
        to_remove_r2a.push_back(bridge);
        return true;
      }),
    active_r2a_bridges_.end());

  auto is_a2r_allowed = [&](const ActiveBridgeA2R & bridge) {
    if (new_config.mode == FilterMode::ALLOW_ALL) return true;
    bool found = false;
    for (const auto & entry : new_config.rules) {
      if (
        entry.topic_name == bridge.topic_name &&
        (entry.direction == BridgeDirection::AGNOCAST_TO_ROS2 ||
         entry.direction == BridgeDirection::BIDIRECTIONAL)) {
        found = true;
        break;
      }
    }
    return (new_config.mode == FilterMode::WHITELIST) ? found : !found;
  };
  active_a2r_bridges_.erase(
    std::remove_if(
      active_a2r_bridges_.begin(), active_a2r_bridges_.end(),
      [&](const ActiveBridgeA2R & bridge) {
        if (is_a2r_allowed(bridge)) {
          return false;
        }
        to_remove_a2r.push_back(bridge);
        return true;
      }),
    active_a2r_bridges_.end());

  if (new_config.mode == FilterMode::WHITELIST) {
    for (const auto & entry : new_config.rules) {
      bool r2a_needed =
        (entry.direction == BridgeDirection::ROS2_TO_AGNOCAST ||
         entry.direction == BridgeDirection::BIDIRECTIONAL);
      bool a2r_needed =
        (entry.direction == BridgeDirection::AGNOCAST_TO_ROS2 ||
         entry.direction == BridgeDirection::BIDIRECTIONAL);

      bool r2a_exists = false;
      if (r2a_needed) {
        for (const auto & bridge : active_r2a_bridges_) {
          if (entry.topic_name == bridge.topic_name) {
            r2a_exists = true;
            break;
          }
        }
      }

      bool a2r_exists = false;
      if (a2r_needed) {
        for (const auto & bridge : active_a2r_bridges_) {
          if (entry.topic_name == bridge.topic_name) {
            a2r_exists = true;
            break;
          }
        }
      }

      if (
        r2a_needed && !r2a_exists && a2r_needed && !a2r_exists &&
        entry.direction == BridgeDirection::BIDIRECTIONAL) {
        to_add.push_back(entry);
      }

      else if (r2a_needed && !r2a_exists) {
        BridgeConfigEntry r2a_entry = entry;
        r2a_entry.direction = BridgeDirection::ROS2_TO_AGNOCAST;
        to_add.push_back(r2a_entry);
      }

      else if (a2r_needed && !a2r_exists) {
        BridgeConfigEntry a2r_entry = entry;
        a2r_entry.direction = BridgeDirection::AGNOCAST_TO_ROS2;
        to_add.push_back(a2r_entry);
      }
    }
  }
}

void BridgeManager::shutdown_removed_bridges(
  const std::vector<ActiveBridgeR2A> & to_remove_r2a,
  const std::vector<ActiveBridgeA2R> & to_remove_a2r)
{
  for (const auto & bridge : to_remove_r2a) {
    if (bridge.plugin_handle) dlclose(bridge.plugin_handle);
  }
  for (const auto & bridge : to_remove_a2r) {
    if (bridge.plugin_handle) dlclose(bridge.plugin_handle);
  }
}

void BridgeManager::launch_new_bridges(const std::vector<BridgeConfigEntry> & to_add)
{
  const pid_t self_pid = getpid();
  for (const auto & entry : to_add) {
    bool is_needed = false;

    if (
      entry.direction == BridgeDirection::ROS2_TO_AGNOCAST ||
      entry.direction == BridgeDirection::BIDIRECTIONAL) {
      union ioctl_get_ext_subscriber_num_args args = {};
      args.topic_name = {entry.topic_name.c_str(), entry.topic_name.size()};
      args.exclude_pid = self_pid;
      if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_SUBSCRIBER_NUM_CMD, &args) < 0) {
        RCLCPP_ERROR(logger_, "Failed to get ext sub count for '%s'", entry.topic_name.c_str());
        continue;
      }
      if (args.ret_ext_subscriber_num > 0) {
        is_needed = true;
        RCLCPP_DEBUG(
          logger_, "R2A bridge needed for '%s' (ext subs: %d)", entry.topic_name.c_str(),
          args.ret_ext_subscriber_num);
      }
    }

    if (
      entry.direction == BridgeDirection::AGNOCAST_TO_ROS2 ||
      entry.direction == BridgeDirection::BIDIRECTIONAL) {
      union ioctl_get_ext_publisher_num_args args = {};
      args.topic_name = {entry.topic_name.c_str(), entry.topic_name.size()};
      args.exclude_pid = self_pid;
      if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_PUBLISHER_NUM_CMD, &args) < 0) {
        RCLCPP_ERROR(logger_, "Failed to get ext pub count for '%s'", entry.topic_name.c_str());
        continue;
      }
      if (args.ret_ext_publisher_num > 0) {
        is_needed = true;
      }
    }

    if (is_needed) {
      BridgeRequest req = {};
      strncpy(req.topic_name, entry.topic_name.c_str(), MAX_NAME_LENGTH - 1);
      strncpy(req.message_type, entry.message_type.c_str(), MAX_NAME_LENGTH - 1);
      req.direction = entry.direction;

      if (req.direction == BridgeDirection::ROS2_TO_AGNOCAST) {
        worker_threads_.emplace_back(&BridgeManager::launch_r2a_bridge_thread, this, req);
      } else if (req.direction == BridgeDirection::AGNOCAST_TO_ROS2) {
        worker_threads_.emplace_back(&BridgeManager::launch_a2r_bridge_thread, this, req);
      } else if (req.direction == BridgeDirection::BIDIRECTIONAL) {
        BridgeRequest req_r2a = req;
        req_r2a.direction = BridgeDirection::ROS2_TO_AGNOCAST;
        worker_threads_.emplace_back(&BridgeManager::launch_r2a_bridge_thread, this, req_r2a);
        BridgeRequest req_a2r = req;
        req_a2r.direction = BridgeDirection::AGNOCAST_TO_ROS2;
        worker_threads_.emplace_back(&BridgeManager::launch_a2r_bridge_thread, this, req_a2r);
      }
    }
  }
}

void BridgeManager::reload_and_update_bridges()
{
  BridgeConfig new_config = parse_bridge_config();

  std::vector<BridgeConfigEntry> to_add;
  std::vector<ActiveBridgeR2A> to_remove_r2a;
  std::vector<ActiveBridgeA2R> to_remove_a2r;
  calculate_bridge_diff(new_config, to_add, to_remove_r2a, to_remove_a2r);
  shutdown_removed_bridges(to_remove_r2a, to_remove_a2r);
  launch_new_bridges(to_add);
  bridge_config_ = new_config;
}

void BridgeManager::check_and_shutdown_idle_bridges()
{
  {
    std::lock_guard<std::mutex> lock(bridge_mutex_);
    const pid_t self_pid = getpid();

    active_r2a_bridges_.erase(
      std::remove_if(
        active_r2a_bridges_.begin(), active_r2a_bridges_.end(),
        [&](const ActiveBridgeR2A & bridge) {
          union ioctl_get_ext_subscriber_num_args args = {};
          args.topic_name = {bridge.topic_name.c_str(), bridge.topic_name.size()};
          args.exclude_pid = self_pid;

          if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_SUBSCRIBER_NUM_CMD, &args) < 0) {
            RCLCPP_ERROR(
              logger_, "Failed to get external subscriber count for '%s'",
              bridge.topic_name.c_str());
            return false;
          }

          if (args.ret_ext_subscriber_num == 0) {
            dlclose(bridge.plugin_handle);
            return true;
          }
          return false;
        }),
      active_r2a_bridges_.end());

    active_a2r_bridges_.erase(
      std::remove_if(
        active_a2r_bridges_.begin(), active_a2r_bridges_.end(),
        [&](const ActiveBridgeA2R & bridge) {
          union ioctl_get_ext_publisher_num_args args = {};
          args.topic_name = {bridge.topic_name.c_str(), bridge.topic_name.size()};
          args.exclude_pid = self_pid;

          if (ioctl(agnocast_fd, AGNOCAST_GET_EXT_PUBLISHER_NUM_CMD, &args) < 0) {
            RCLCPP_ERROR(
              logger_, "Failed to get external publisher count for '%s'",
              bridge.topic_name.c_str());
            return false;
          }

          if (args.ret_ext_publisher_num == 0) {
            dlclose(bridge.plugin_handle);
            return true;
          }
          return false;
        }),
      active_a2r_bridges_.end());
  }
}

void BridgeManager::check_and_shutdown_daemon_if_idle()
{
  {
    std::lock_guard<std::mutex> lock(bridge_mutex_);
    if (!active_r2a_bridges_.empty() || !active_a2r_bridges_.empty()) {
      return;
    }
  }

  struct ioctl_get_active_process_num_args args = {};
  if (ioctl(agnocast_fd, AGNOCAST_GET_ACTIVE_PROCESS_NUM_CMD, &args) < 0) {
    RCLCPP_ERROR(logger_, "Failed to get active process count from kernel module.");
    return;
  }

  if (args.ret_active_process_num <= 1) {
    rclcpp::shutdown();
  }
}

void BridgeManager::shutdown_manager_internal()
{
  if (spin_thread_.joinable()) {
    spin_thread_.join();
  }

  for (auto & th : worker_threads_) {
    if (th.joinable()) {
      th.join();
    }
  }

  for (auto & bridge : active_r2a_bridges_) {
    dlclose(bridge.plugin_handle);
  }
  active_r2a_bridges_.clear();

  for (auto & bridge : active_a2r_bridges_) {
    dlclose(bridge.plugin_handle);
  }
  active_a2r_bridges_.clear();

  mq_close(mq_);
  mq_unlink(mq_name_str_.c_str());
}

BridgeConfig BridgeManager::parse_bridge_config()
{
  RCLCPP_INFO(logger_, "Loading bridge filter configuration.");

  BridgeConfig config;
  const char * file_path = getenv("AGNOCAST_BRIDGE_FILTER_FILE");
  if (!file_path) {
    RCLCPP_WARN(
      logger_, "AGNOCAST_BRIDGE_FILTER_FILE not set. Defaulting to ALLOW_ALL filter mode.");
    config.mode = FilterMode::ALLOW_ALL;
    return config;
  }

  YAML::Node yaml_doc;
  try {
    yaml_doc = YAML::LoadFile(file_path);
  } catch (const YAML::Exception & e) {
    RCLCPP_ERROR(logger_, "Failed to parse YAML filter file '%s': %s", file_path, e.what());
    config.mode = FilterMode::ALLOW_ALL;
    return config;
  }

  if (yaml_doc["filter_mode"] && yaml_doc["filter_mode"].IsScalar()) {
    std::string mode_str = yaml_doc["filter_mode"].as<std::string>();
    if (mode_str == "whitelist") {
      config.mode = FilterMode::WHITELIST;
    } else {
      config.mode = FilterMode::BLACKLIST;
    }
  } else {
    config.mode = FilterMode::BLACKLIST;
  }

  RCLCPP_INFO(
    logger_, "MODE: %s", (config.mode == FilterMode::WHITELIST) ? "WHITELIST" : "BLACKLIST");

  if (!yaml_doc["rules"] || !yaml_doc["rules"].IsMap()) {
    RCLCPP_ERROR(logger_, "No valid rules found in filter file '%s'.", file_path);
    return config;
  }

  YAML::Node rules = yaml_doc["rules"];
  for (const auto & msg_type_pair : rules) {
    if (!msg_type_pair.first.IsScalar() || !msg_type_pair.second.IsMap()) {
      RCLCPP_ERROR(logger_, "Skipping invalid rule structure (expected MsgType -> Map).");
      continue;
    }

    std::string message_type = msg_type_pair.first.as<std::string>();
    YAML::Node direction_map = msg_type_pair.second;

    for (const auto & direction_pair : direction_map) {
      if (!direction_pair.first.IsScalar() || !direction_pair.second.IsSequence()) {
        RCLCPP_ERROR(logger_, "Skipping invalid rule structure (expected Direction -> List).");
        continue;
      }

      std::string direction_str = direction_pair.first.as<std::string>();
      YAML::Node topic_list = direction_pair.second;

      BridgeDirection direction_enum;
      if (direction_str == "r2a") {
        direction_enum = BridgeDirection::ROS2_TO_AGNOCAST;
      } else if (direction_str == "a2r") {
        direction_enum = BridgeDirection::AGNOCAST_TO_ROS2;
      } else if (direction_str == "bidirectional") {
        direction_enum = BridgeDirection::BIDIRECTIONAL;
      } else {
        RCLCPP_ERROR(logger_, "Skipping unknown direction key: %s", direction_str.c_str());
        continue;
      }

      for (const auto & topic_node : topic_list) {
        if (!topic_node.IsScalar()) {
          RCLCPP_ERROR(logger_, "Skipping invalid topic name (not a scalar).");
          continue;
        }

        std::string topic_name = topic_node.as<std::string>();

        BridgeConfigEntry entry;
        entry.topic_name = topic_name;
        entry.message_type = message_type;
        entry.direction = direction_enum;

        config.rules.push_back(entry);
      }
    }
  }

  return config;
}

std::unique_ptr<rclcpp::Executor> BridgeManager::select_executor()
{
  std::unique_ptr<rclcpp::Executor> executor;
  const char * executor_type_env = getenv("AGNOCAST_EXECUTOR_TYPE");
  std::string executor_type = executor_type_env ? executor_type_env : "single";

  if (executor_type == "multi") {
    RCLCPP_INFO(logger_, "[BRIDGE MANAGER DAEMON] Using MultiThreadedAgnocastExecutor.");
    size_t num_threads = 0;
    const char * thread_num_env = getenv("AGNOCAST_MULTI_THREAD_NUM");

    if (thread_num_env) {
      try {
        num_threads = std::stoul(thread_num_env);
      } catch (const std::invalid_argument & e) {
        RCLCPP_ERROR(
          logger_,
          "[BRIDGE MANAGER DAEMON] Invalid AGNOCAST_MULTI_THREAD_NUM. Using hardware concurrency.");
      } catch (const std::out_of_range & e) {
        RCLCPP_ERROR(
          logger_,
          "[BRIDGE MANAGER DAEMON] AGNOCAST_MULTI_THREAD_NUM out of range. Using hardware "
          "concurrency.");
      }
    }

    if (num_threads == 0) {
      num_threads = std::thread::hardware_concurrency();
      if (num_threads == 0) {
        RCLCPP_ERROR(
          logger_,
          "[BRIDGE MANAGER DAEMON] Could not detect hardware concurrency. Defaulting to 4 "
          "threads.");
        num_threads = 4;
      }
      RCLCPP_INFO(
        logger_, "[BRIDGE MANAGER DAEMON] Using default hardware concurrency: %zu threads",
        num_threads);
    }

    RCLCPP_INFO(
      logger_, "[BRIDGE MANAGER DAEMON] Using MultiThreadedAgnocastExecutor with %zu threads.",
      num_threads);
    rclcpp::ExecutorOptions options;
    executor = std::make_unique<agnocast::MultiThreadedAgnocastExecutor>(options, num_threads);
  } else if (executor_type == "isolated") {
    RCLCPP_INFO(logger_, "[BRIDGE MANAGER DAEMON] Using CallbackIsolatedAgnocastExecutor.");
    executor = std::make_unique<agnocast::CallbackIsolatedAgnocastExecutor>();
  } else {
    RCLCPP_INFO(logger_, "[BRIDGE MANAGER DAEMON] Using SingleThreadedAgnocastExecutor (default).");
    executor = std::make_unique<agnocast::SingleThreadedAgnocastExecutor>();
  }

  return executor;
}

void BridgeManager::sighup_handler(int signum)
{
  if (signum == SIGHUP) {
    reload_filter_request_.store(true);
  }
}

}  // namespace agnocast
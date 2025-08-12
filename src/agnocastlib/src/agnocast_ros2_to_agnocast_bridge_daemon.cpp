#include "agnocast/agnocast_ros2_to_agnocast_bridge_daemon.hpp"

#include "agnocast/agnocast_ioctl.hpp"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <algorithm>
#include <csignal>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

rclcpp::Node::SharedPtr g_node = nullptr;
std::vector<rclcpp::SubscriptionBase::SharedPtr> g_subscriptions;

void signal_handler(int signum)
{
  if (g_node) {
    RCLCPP_INFO(
      g_node->get_logger(), "Interrupt signal (%d) received. Initiating shutdown...", signum);
  }
  rclcpp::shutdown();
}

namespace agnocast
{
class FileDescriptorGuard
{
public:
  explicit FileDescriptorGuard(const char * pathname) : fd_(open(pathname, O_RDWR)) {}

  // Closes the file in the destructor.
  ~FileDescriptorGuard()
  {
    if (isValid()) {
      close(fd_);
    }
  }

  FileDescriptorGuard(const FileDescriptorGuard &) = delete;
  FileDescriptorGuard & operator=(const FileDescriptorGuard &) = delete;

  int get() const { return fd_; }

  bool isValid() const { return fd_ >= 0; }

private:
  int fd_;
};

void monitor_subscriber_count(const std::string & topic_name)
{
  // Use the RAII wrapper to manage the file descriptor.
  FileDescriptorGuard agnocast_fd("/dev/agnocast");
  if (!agnocast_fd.isValid()) {
    RCLCPP_ERROR(g_node->get_logger(), "Failed to open /dev/agnocast. Shutting down.");
    rclcpp::shutdown();
    return;
  }

  while (rclcpp::ok()) {
    union ioctl_get_subscriber_num_args get_subscriber_count_args = {};
    get_subscriber_count_args.topic_name = {topic_name.c_str(), topic_name.size()};

    if (
      ioctl(agnocast_fd.get(), AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) == 0) {
      if (get_subscriber_count_args.ret_subscriber_num == 0) {
        RCLCPP_INFO(
          g_node->get_logger(), "Subscriber count for topic '%s' is 0. Shutting down daemon.",
          topic_name.c_str());
        rclcpp::shutdown();  // Trigger shutdown
        break;
      }
    } else {
      RCLCPP_WARN(g_node->get_logger(), "ioctl to get subscriber count failed.");
    }

    std::this_thread::sleep_for(std::chrono::seconds(1));
  }
  // The file descriptor is automatically closed here by the FileDescriptorGuard destructor.
}

std::map<std::string, BridgeSetupFunction> & get_bridge_factory_map()
{
  static std::map<std::string, BridgeSetupFunction> factory_map;
  return factory_map;
}

inline rclcpp::QoS parse_qos_from_args(int argc, const char * argv[])
{
  rclcpp::QoS qos{rclcpp::KeepLast(10)};

  for (int i = 3; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--depth" && i + 1 < argc) {
      qos.keep_last(std::stoul(argv[++i]));
    } else if (arg == "--durability" && i + 1 < argc) {
      std::string val = argv[++i];
      if (val == "transient_local") {
        qos.transient_local();
      } else {
        qos.durability(rclcpp::DurabilityPolicy::Volatile);
      }
    } else if (arg == "--reliability" && i + 1 < argc) {
      std::string val = argv[++i];
      if (val == "reliable") {
        qos.reliable();
      } else {
        qos.best_effort();
      }
    }
  }
  return qos;
}

}  // namespace agnocast

int main(int argc, char * argv[])
{
  if (setsid() == -1) {
    perror("setsid failed");
    return EXIT_FAILURE;
  }

  signal(SIGINT, signal_handler);
  signal(SIGTERM, signal_handler);

  if (argc < 3) {
    std::cerr << "Usage: " << argv[0] << " <topic_name> <message_type> [qos_options]" << std::endl;
    return EXIT_FAILURE;
  }

  const std::string topic_name = argv[1];
  const std::string message_type = argv[2];
  rclcpp::QoS qos = agnocast::parse_qos_from_args(argc, const_cast<const char **>(argv));

  std::string node_name_suffix = topic_name;
  std::replace(node_name_suffix.begin(), node_name_suffix.end(), '/', '_');
  // Ensure node name is valid by removing leading underscore if topic starts with '/'
  if (!node_name_suffix.empty() && node_name_suffix.front() == '_') {
    node_name_suffix.erase(0, 1);
  }

  rclcpp::init(argc, argv);

  g_node = rclcpp::Node::make_shared("agnocast_bridge_" + node_name_suffix);
  auto logger = g_node->get_logger();

  auto & factory = agnocast::get_bridge_factory_map();
  auto it = factory.find(message_type);
  if (it == factory.end()) {
    RCLCPP_FATAL(logger, "Message type '%s' not supported.", message_type.c_str());
    rclcpp::shutdown();
    return EXIT_FAILURE;
  }
  it->second(g_node, topic_name, qos);

  std::thread monitor_thread(agnocast::monitor_subscriber_count, topic_name);

  RCLCPP_INFO(logger, "Bridge daemon started for topic: %s", topic_name.c_str());
  rclcpp::spin(g_node);  // Blocks until rclcpp::shutdown() is called.

  // Wait for the monitor thread to finish its last loop and exit cleanly.
  if (monitor_thread.joinable()) {
    monitor_thread.join();
  }

  // Clean up global resources.
  g_subscriptions.clear();
  g_node = nullptr;

  RCLCPP_INFO(logger, "Bridge daemon for topic '%s' has shut down gracefully.", topic_name.c_str());

  return EXIT_SUCCESS;
}
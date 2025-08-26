#include "agnocast/agnocast_bridge_daemon.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <unistd.h>

#include <csignal>

class DynamicLibraryGuard
{
public:
  explicit DynamicLibraryGuard(const char * path) : handle_(dlopen(path, RTLD_NOW | RTLD_GLOBAL)) {}
  ~DynamicLibraryGuard()
  {
    if (handle_) {
      dlclose(handle_);
    }
  }

  void * get() const { return handle_; }

  DynamicLibraryGuard(const DynamicLibraryGuard &) = delete;
  DynamicLibraryGuard & operator=(const DynamicLibraryGuard &) = delete;

private:
  void * handle_;
};

// Temporary implementation.
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

namespace agnocast
{

std::map<std::string, BridgeComponents> g_active_bridges;
std::mutex g_bridges_mutex;

// Temporary implementation.
void monitor_subscriber_count(const std::string & topic_name)
{
  FileDescriptorGuard agnocast_fd("/dev/agnocast");
  if (!agnocast_fd.isValid()) {
    std::cerr << "Failed to open /dev/agnocast: " << strerror(errno) << std::endl;
    rclcpp::shutdown();
    return;
  }

  while (rclcpp::ok()) {
    union ioctl_get_subscriber_num_args get_subscriber_count_args = {};
    get_subscriber_count_args.topic_name = {topic_name.c_str(), topic_name.size()};

    if (
      ioctl(agnocast_fd.get(), AGNOCAST_GET_SUBSCRIBER_NUM_CMD, &get_subscriber_count_args) == 0) {
      if (get_subscriber_count_args.ret_subscriber_num == 0) {
        std::cerr << "Subscriber count for topic '" << topic_name << "' is 0. Shutting down daemon."
                  << std::endl;
        rclcpp::shutdown();
      }
    } else {
      std::cerr << "ioctl to get subscriber count failed: " << strerror(errno) << std::endl;
    }

    std::this_thread::sleep_for(std::chrono::seconds(1));
  }
}

}  // namespace agnocast

void signal_handler(int signum)
{
  std::cout << "Received signal " << signum << ", shutting down ROS 2..." << std::endl;
  rclcpp::shutdown();
}

bool parse_arguments(
  int argc, char * argv[], BridgeArgs & args, std::string & lib_path, std::string & mangled_name)
{
  if (argc < 7) {
    std::cerr << "[Bridge Daemon] Error: Not enough arguments." << std::endl;
    return false;
  }

  lib_path = argv[1];
  mangled_name = argv[2];
  std::string topic_name_str = argv[3];

  snprintf(args.topic_name, sizeof(args.topic_name), "%s", topic_name_str.c_str());

  try {
    args.qos_history = std::stoi(argv[4]);
    args.qos_depth = std::stoi(argv[5]);
    args.qos_reliability = std::stoi(argv[6]);
  } catch (const std::exception & e) {
    std::cerr << "[Bridge Daemon] Error: Invalid QoS arguments. " << e.what() << std::endl;
    return false;
  }
  return true;
}

void setup_process()
{
  if (setsid() == -1) {
    perror("setsid failed");
    exit(EXIT_FAILURE);
  }

  struct sigaction sa = {};
  sa.sa_handler = signal_handler;
  sigemptyset(&sa.sa_mask);
  sigaction(SIGINT, &sa, nullptr);
  sigaction(SIGTERM, &sa, nullptr);
}

int main(int argc, char * argv[])
{
  setup_process();
  std::cout << "[Bridge Daemon] Started with PID: " << getpid() << std::endl;

  BridgeArgs args{};
  std::string shared_lib_path, mangled_name;
  if (!parse_arguments(argc, argv, args, shared_lib_path, mangled_name)) {
    return EXIT_FAILURE;
  }

  DynamicLibraryGuard library(shared_lib_path.c_str());
  if (!library.get()) {
    std::cerr << "[Bridge Daemon] dlopen failed: " << dlerror() << std::endl;
    return EXIT_FAILURE;
  }

  void * func_ptr = dlsym(library.get(), mangled_name.c_str());
  if (!func_ptr) {
    std::cerr << "[Bridge Daemon] dlsym failed: " << dlerror() << std::endl;
    return EXIT_FAILURE;
  }
  auto bridge_function = reinterpret_cast<BridgeFn>(func_ptr);

  rclcpp::init(0, nullptr);
  auto executor = std::make_shared<rclcpp::executors::MultiThreadedExecutor>();

  bridge_function(args, executor);
  std::cout << "[Bridge Daemon] Successfully started bridge for topic: " << args.topic_name
            << std::endl;

  std::thread monitor_thread(agnocast::monitor_subscriber_count, std::string(args.topic_name));

  executor->spin();
  rclcpp::shutdown();

  if (monitor_thread.joinable()) {
    monitor_thread.join();
  }

  std::cout << "[Bridge Daemon] Shutting down for topic: " << args.topic_name << std::endl;

  return EXIT_SUCCESS;
}

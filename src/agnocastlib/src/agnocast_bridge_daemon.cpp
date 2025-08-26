#include "agnocast/agnocast_bridge_daemon.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <unistd.h>

#include <csignal>

namespace agnocast
{

std::map<std::string, BridgeComponents> g_active_bridges;
std::mutex g_bridges_mutex;

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
        rclcpp::shutdown();  // Trigger shutdown
        break;
      }
    } else {
      std::cerr << "ioctl to get subscriber count failed: " << strerror(errno) << std::endl;
    }

    std::this_thread::sleep_for(std::chrono::seconds(1));
  }
  // The file descriptor is automatically closed here by the FileDescriptorGuard destructor.
}

}  // namespace agnocast

void signal_handler(int signum)
{
  std::cout << "Received signal " << signum << ", shutting down ROS 2..." << std::endl;
  rclcpp::shutdown();
}

int main(int argc, char * argv[])
{
  if (setsid() == -1) {
    perror("setsid failed");
    return EXIT_FAILURE;
  }

  struct sigaction sa;
  sa.sa_handler = signal_handler;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = 0;
  sigaction(SIGINT, &sa, nullptr);
  sigaction(SIGTERM, &sa, nullptr);

  std::cout << "Bridge daemon process started with PID: " << getpid() << std::endl;

  if (argc < 7) {  // 引数は argv[0], argv[1], argv[2], argv[3]
    std::cerr << "Error: Usage: " << argv[0] << " <shared_lib_path> <mangled_name> <topic_name>"
              << std::endl;
    return EXIT_FAILURE;
  }

  rclcpp::init(0, nullptr);

  auto executor = std::make_shared<rclcpp::executors::MultiThreadedExecutor>();

  const char * shared_lib_path = argv[1];
  const char * mangled_name = argv[2];
  const std::string topic_name = argv[3];

  void * handle = dlopen(shared_lib_path, RTLD_NOW | RTLD_GLOBAL);
  if (!handle) {
    std::cerr << "[Daemon] dlopen failed: " << dlerror() << std::endl;
    return EXIT_FAILURE;
  }

  void * func_ptr = dlsym(handle, mangled_name);
  if (!func_ptr) {
    std::cerr << "[Daemon] dlsym failed: " << dlerror() << std::endl;
    dlclose(handle);
    return EXIT_FAILURE;
  }

  BridgeFn bridge_function = reinterpret_cast<BridgeFn>(func_ptr);

  BridgeArgs args{};
  strncpy(args.topic_name, argv[3], sizeof(args.topic_name) - 1);
  args.qos_history = std::stoi(argv[4]);
  args.qos_depth = std::stoi(argv[5]);
  args.qos_reliability = std::stoi(argv[6]);

  bridge_function(args, executor);

  std::thread monitor_thread(agnocast::monitor_subscriber_count, std::ref(topic_name));

  std::cout << "[Bridge Process] Starting executor spin for topic: " << std::endl;
  executor->spin();

  if (monitor_thread.joinable()) {
    std::cout << "[Bridge Process] Waiting for monitor thread to finish." << std::endl;
    monitor_thread.join();
  }

  std::cout << "[Bridge Process] Shutting down for topic: " << topic_name << std::endl;
  dlclose(handle);
  exit(EXIT_SUCCESS);
}

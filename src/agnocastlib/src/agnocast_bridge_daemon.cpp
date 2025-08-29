#include "agnocast/agnocast_bridge_daemon.hpp"

#include "agnocast/agnocast_ioctl.hpp"
#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <unistd.h>

#include <csignal>

namespace agnocast
{

std::map<std::string, BridgeComponents> g_active_bridges;
std::mutex g_bridges_mutex;

}  // namespace agnocast

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

  const std::string topic_info_mq_name = agnocast::create_mq_name_for_topic_info();
  mqd_t topic_info_mq = mq_open(topic_info_mq_name.c_str(), O_WRONLY);

  if (topic_info_mq != (mqd_t)-1) {
    agnocast::MqMsgTopicInfo msg_to_send = {};
    msg_to_send.pid = getpid();
    strncpy(msg_to_send.topic_name, args.topic_name, sizeof(msg_to_send.topic_name) - 1);
    msg_to_send.topic_name[sizeof(msg_to_send.topic_name) - 1] = '\0';

    if (
      mq_send(
        topic_info_mq, reinterpret_cast<const char *>(&msg_to_send), sizeof(msg_to_send), 0) ==
      -1) {
      std::cerr << "mq_send failed: " << strerror(errno) << std::endl;
    }
    mq_close(topic_info_mq);
  } else {
    std::cerr << "mq_open failed for topic_info_mq: " << strerror(errno) << std::endl;
  }

  executor->spin();
  rclcpp::shutdown();

  std::cout << "[Bridge Daemon] Shutting down for topic: " << args.topic_name << std::endl;

  return EXIT_SUCCESS;
}

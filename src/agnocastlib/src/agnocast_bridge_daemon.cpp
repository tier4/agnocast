#include "agnocast/agnocast_bridge_daemon.hpp"

#include "agnocast/agnocast.hpp"
#include "agnocast/agnocast_ioctl.hpp"
#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>
#include <fcntl.h>
#include <link.h>
#include <mqueue.h>
#include <sys/wait.h>
#include <unistd.h>

#include <csignal>

namespace agnocast
{

std::map<std::string, BridgeComponents> g_active_bridges;
std::mutex g_bridges_mutex;

std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> g_executor;

struct PhdrFindBaseData
{
  const char * target_lib_name;
  uintptr_t base_addr;
};

static int find_base_callback(struct dl_phdr_info * info, size_t /*size*/, void * data)
{
  PhdrFindBaseData * find_data = (PhdrFindBaseData *)data;
  if (info->dlpi_name && strcmp(info->dlpi_name, find_data->target_lib_name) == 0) {
    find_data->base_addr = info->dlpi_addr;
    return 1;
  }
  return 0;
}

// ros2 topic pub --qos-reliability reliable /my_topic
// agnocast_sample_interfaces/msg/DynamicSizeArray "{id: 1, data: [10, 20, 30]}"

void bridge_process_main(const ControlMsg & msg)
{
  rclcpp::init(0, nullptr);

  g_executor = std::make_shared<rclcpp::executors::MultiThreadedExecutor>();

  const char * mempool_size_env = std::getenv("AGNOCAST_MEMPOOL_SIZE");
  size_t shm_size = mempool_size_env ? std::stoul(mempool_size_env) : 67108864;

  union ioctl_add_process_args add_process_args = {};
  add_process_args.shm_size = shm_size;
  std::cerr << "[Bridge Process] Using shared memory size: " << shm_size << " bytes" << std::endl;
  if (ioctl(agnocast_fd, AGNOCAST_ADD_PROCESS_CMD, &add_process_args) < 0) {
    std::cerr << "[Bridge Process Error] AGNOCAST_ADD_PROCESS_CMD failed: " << strerror(errno)
              << std::endl;
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  void * mempool_ptr = map_writable_area(getpid(), add_process_args.ret_addr, shm_size);
  std::cerr << "[Bridge Process] Mapped memory pool at address: " << std::hex
            << reinterpret_cast<uintptr_t>(mempool_ptr) << std::endl;

  if (mempool_ptr == nullptr) {
    std::cerr << "[Bridge Process Error] map_writable_area failed" << std::endl;
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  void * handle = dlopen(msg.library_name, RTLD_LAZY);
  if (!handle) {
    exit(EXIT_FAILURE);
  }

  PhdrFindBaseData find_data = {msg.library_name, 0};
  dl_iterate_phdr(find_base_callback, &find_data);
  if (find_data.base_addr == 0) {
    dlclose(handle);
    exit(EXIT_FAILURE);
  }

  uintptr_t func_addr = find_data.base_addr + msg.function_offset;
  BridgeFn bridge_function = reinterpret_cast<BridgeFn>(func_addr);

  bridge_function(msg.args);

  std::cout << "[Bridge Process] Starting executor spin for topic: " << msg.args.topic_name
            << std::endl;
  g_executor->spin();

  dlclose(handle);
  close(agnocast_fd);
  rclcpp::shutdown();
  std::cout << "[Bridge Process] Shutting down for topic: " << msg.args.topic_name << std::endl;
  exit(EXIT_SUCCESS);
}

void bridge_daemon_main(mqd_t mq_read)
{
  signal(SIGCHLD, SIG_IGN);

  std::cout << "[Bridge Daemon] PID: " << getpid() << ". Ready to launch bridge processes..."
            << std::endl;

  while (true) {
    ControlMsg msg{};
    ssize_t bytes_read = mq_receive(mq_read, reinterpret_cast<char *>(&msg), sizeof(msg), nullptr);
    if (bytes_read <= 0) {
      break;
    }

    if (msg.opcode == ControlMsg::StartBridge) {
      pid_t pid = fork();
      if (pid < 0) {
        std::cerr << "[Bridge Daemon] fork failed: " << strerror(errno) << std::endl;
        continue;
      }
      if (pid == 0) {
        mq_close(mq_read);
        bridge_process_main(msg);
      }
      std::cout << "[Bridge Daemon] Launched a new bridge process with PID " << pid
                << " for topic: " << msg.args.topic_name << std::endl;

    } else if (msg.opcode == ControlMsg::Shutdown) {
      std::cout << "[Bridge Daemon] Received shutdown command. Exiting." << std::endl;
      break;
    }
  }

  mq_close(mq_read);
  std::cout << "[Bridge Daemon] Daemon has finished." << std::endl;
  exit(EXIT_SUCCESS);
}

}  // namespace agnocast
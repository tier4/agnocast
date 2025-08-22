#include "agnocast/agnocast_bridge_daemon.hpp"

#include "rclcpp/rclcpp.hpp"

#include <dlfcn.h>  // dlopen, dlsym, dlerror を使うために追加
#include <link.h>   // dl_iterate_phdr を使うために追加
#include <mqueue.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <iostream>
#include <thread>
#include <vector>

namespace agnocast
{
std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> g_executor;
std::thread g_spin_thread;

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

void bridge_daemon_main(mqd_t mq_read)
{
  if (setsid() == -1) {
    std::cerr << "setsid failed for daemon: " << strerror(errno) << std::endl;
    exit(EXIT_FAILURE);
  }

  rclcpp::init(0, nullptr);

  g_executor = std::make_shared<rclcpp::executors::MultiThreadedExecutor>();
  g_spin_thread = std::thread([]() { g_executor->spin(); });

  std::cout << "[Bridge Daemon] PID: " << getpid() << ". Waiting for commands..." << std::endl;

  while (rclcpp::ok()) {
    ControlMsg msg{};
    ssize_t bytes_read = mq_receive(mq_read, reinterpret_cast<char *>(&msg), sizeof(msg), nullptr);

    if (bytes_read < 0) {
      if (errno == EAGAIN) continue;
      std::cerr << "[Bridge Daemon] mq_receive failed. Shutting down." << std::endl;
      break;
    }

    if (static_cast<size_t>(bytes_read) != sizeof(ControlMsg)) {
      std::cerr << "[Bridge Daemon] Received malformed message." << std::endl;
      continue;
    }

    if (msg.opcode == ControlMsg::StartBridge) {
      std::cout << "[Bridge Daemon] Received StartBridge for topic: " << msg.args.topic_name
                << std::endl;
      std::cout << "[Bridge Daemon] Library: " << msg.library_name << ", Offset: 0x" << std::hex
                << msg.function_offset << std::dec << std::endl;

      void * handle = dlopen(msg.library_name, RTLD_LAZY);
      if (!handle) {
        std::cerr << "[Bridge Daemon Error] dlopen failed for " << msg.library_name << ": "
                  << dlerror() << std::endl;
        continue;
      }

      PhdrFindBaseData find_data = {msg.library_name, 0};
      dl_iterate_phdr(find_base_callback, &find_data);

      if (find_data.base_addr == 0) {
        std::cerr << "[Bridge Daemon Error] Could not find library " << msg.library_name
                  << " in my address space after dlopen." << std::endl;
        dlclose(handle);
        continue;
      }

      uintptr_t func_addr_in_daemon = find_data.base_addr + msg.function_offset;
      BridgeFn bridge_function = reinterpret_cast<BridgeFn>(func_addr_in_daemon);

      std::cout << "[Bridge Daemon] Reconstructed function pointer at 0x" << std::hex
                << func_addr_in_daemon << std::dec << ". Calling bridge function..." << std::endl;
      bridge_function(msg.args);

      // 注意:
      // 本番環境では、ブリッジが不要になった際にdlclose(handle)を呼び出すための管理機構が必要です。
      // ^ ^ ^ ^ ^ 修正箇所 ^ ^ ^ ^ ^
    }
  }

  std::cout << "[Bridge Daemon] Shutting down..." << std::endl;
  g_executor->cancel();
  g_spin_thread.join();
  rclcpp::shutdown();
  mq_close(mq_read);

  std::cout << "[Bridge Daemon] Daemon has finished." << std::endl;
  exit(EXIT_SUCCESS);
}

}  // namespace agnocast
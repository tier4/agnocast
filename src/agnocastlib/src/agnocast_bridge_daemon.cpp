#include "agnocast/agnocast_bridge_daemon.hpp"

#include <dlfcn.h>

extern int agnocast_fd;

namespace agnocast
{

std::shared_ptr<rclcpp::executors::MultiThreadedExecutor> g_executor;

void bridge_process_main(const MqMsgBridge & msg)
{
  rclcpp::init(0, nullptr);

  g_executor = std::make_shared<rclcpp::executors::MultiThreadedExecutor>();

  if (msg.fn_ptr == 0) {
    std::cerr << "[Bridge Process Error] Received a null function pointer!" << std::endl;
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  BridgeFn entry_func = nullptr;

  if (std::strcmp(msg.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    std::cout << "[Bridge Process] Using direct fn_ptr for executable symbol." << std::endl;
    entry_func = reinterpret_cast<BridgeFn>(msg.fn_ptr);
  } else {
    const char * lib_path = msg.shared_lib_path;
    void * handle = dlopen(lib_path, RTLD_NOW);

    if (!handle) {
      std::cerr << "[Bridge Process Error] dlopen failed for " << lib_path << ": " << dlerror()
                << std::endl;
      close(agnocast_fd);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }
    std::cout << "[Bridge Process] Looking up symbol via dlsym: " << msg.symbol_name << std::endl;
    void * raw_func = dlsym(handle, msg.symbol_name);

    if (!raw_func) {
      std::cerr << "[Bridge Process Error] dlsym failed for symbol " << msg.symbol_name << " in "
                << lib_path << ": " << dlerror() << std::endl;
      dlclose(handle);
      close(agnocast_fd);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }

    entry_func = reinterpret_cast<BridgeFn>(raw_func);
  }

  std::cout << "[Bridge Process] Calling bridge entry function..." << std::endl;

  try {
    entry_func(msg.args);
    std::cout << "[Bridge Process] Starting executor spin for topic: " << msg.args.topic_name
              << std::endl;

    g_executor->spin();

  } catch (const std::exception & e) {
    std::cerr << "[Bridge Process FATAL ERROR] Unhandled std::exception: " << e.what()
              << " for topic: " << msg.args.topic_name << std::endl;
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  } catch (...) {
    std::cerr << "[Bridge Process FATAL ERROR] Unhandled unknown exception"
              << " for topic: " << msg.args.topic_name << std::endl;
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  close(agnocast_fd);
  rclcpp::shutdown();
  std::cout << "[Bridge Process] Shutting down for topic: " << msg.args.topic_name << std::endl;
  exit(EXIT_SUCCESS);
}

}
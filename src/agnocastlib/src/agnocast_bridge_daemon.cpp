#include "agnocast/agnocast_bridge_daemon.hpp"

#include "rclcpp/rclcpp.hpp"

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
      std::cerr << "[Bridge Daemon] mq_receive failed. Shutting down." << std::endl;
      break;
    }

    if (static_cast<size_t>(bytes_read) != sizeof(ControlMsg)) {
      std::cerr << "[Bridge Daemon] Received malformed message." << std::endl;
      continue;
    }

    if (msg.opcode == ControlMsg::StartBridge) {
      std::cout << "[Bridge Daemon] Received StartBridge command for topic: " << msg.args.topic_name
                << std::endl;

      std::cout << "[Daemon Debug] Received fn_ptr value: 0x" << std::hex << msg.fn_ptr << std::dec
                << std::endl;

      if (msg.fn_ptr == 0) {
        std::cerr << "[Bridge Daemon Error] Received a NULL function pointer. Cannot proceed."
                  << std::endl;
        continue;
      }

      std::cout << "[Bridge Daemon] Starting bridge for topic: " << msg.args.topic_name
                << std::endl;
      auto fn = reinterpret_cast<BridgeFn>(msg.fn_ptr);
      std::cout << "[Bridge Daemon] Calling bridge function for topic: " << msg.args.topic_name
                << std::endl;
      fn(msg.args);
      std::cout << "[Bridge Daemon] Bridge function executed for topic: " << msg.args.topic_name
                << std::endl;
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
#include "agnocast/agnocast_bridge_daemon.hpp"

#include <dlfcn.h>
#include <signal.h>

extern int agnocast_fd;

namespace agnocast
{

QoSFlat flatten_qos(const rclcpp::QoS & qos)
{
  QoSFlat out{};
  const auto & rmw_qos = qos.get_rmw_qos_profile();
  out.depth = rmw_qos.depth;
  out.history = (rmw_qos.history == RMW_QOS_POLICY_HISTORY_KEEP_ALL) ? 1 : 0;
  out.reliability = (rmw_qos.reliability == RMW_QOS_POLICY_RELIABILITY_RELIABLE) ? 1 : 2;
  out.durability = (rmw_qos.durability == RMW_QOS_POLICY_DURABILITY_TRANSIENT_LOCAL) ? 1 : 2;
  return out;
}

rclcpp::QoS reconstruct_qos(const QoSFlat & q)
{
  rclcpp::QoS qos(q.depth);
  if (q.history == 1) {
    qos.keep_all();
  }
  if (q.reliability == 1) {
    qos.reliable();
  } else if (q.reliability == 2) {
    qos.best_effort();
  }
  if (q.durability == 1) {
    qos.transient_local();
  }
  return qos;
}

void bridge_process_main(const MqMsgBridge & msg)
{
  std::signal(SIGPIPE, SIG_IGN);

  rclcpp::init(0, nullptr);
  rclcpp::executors::SingleThreadedExecutor executor;

  auto logger = rclcpp::get_logger("agnocast_bridge_daemon");

  if (msg.fn_ptr == 0) {
    RCLCPP_FATAL(logger, "[Bridge Process Error] Received a null function pointer!");
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  BridgeFn entry_func = nullptr;

  if (std::strcmp(msg.symbol_name, "__MAIN_EXECUTABLE__") == 0) {
    entry_func = reinterpret_cast<BridgeFn>(msg.fn_ptr);
  } else {
    const char * lib_path = msg.shared_lib_path;
    void * handle = dlopen(lib_path, RTLD_NOW);

    if (!handle) {
      RCLCPP_FATAL(logger, "[Bridge Process Error] dlopen failed for %s: %s", lib_path, dlerror());
      close(agnocast_fd);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }
    void * raw_func = dlsym(handle, msg.symbol_name);

    if (!raw_func) {
      RCLCPP_FATAL(
        logger, "[Bridge Process Error] dlsym failed for symbol %s in %s: %s", msg.symbol_name,
        lib_path, dlerror());
      dlclose(handle);
      close(agnocast_fd);
      rclcpp::shutdown();
      exit(EXIT_FAILURE);
    }

    entry_func = reinterpret_cast<BridgeFn>(raw_func);
  }

  try {
    auto node = entry_func(msg.args);
    executor.add_node(node);
    executor.spin();
  } catch (const std::exception & e) {
    RCLCPP_FATAL(
      logger, "[Bridge Process FATAL ERROR] Unhandled std::exception: %s for topic: %s", e.what(),
      msg.args.topic_name);
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  } catch (...) {
    RCLCPP_FATAL(
      logger, "[Bridge Process FATAL ERROR] Unhandled unknown exception for topic: %s",
      msg.args.topic_name);
    close(agnocast_fd);
    rclcpp::shutdown();
    exit(EXIT_FAILURE);
  }

  close(agnocast_fd);
  rclcpp::shutdown();
  exit(EXIT_SUCCESS);
}

bool get_topic_publishers(
  const std::string & topic_name, std::vector<std::string> & publisher_names, rclcpp::Logger logger)
{
  publisher_names.clear();

  std::vector<struct topic_info_ret> info_buffer(MAX_TOPIC_INFO_RET_NUM);

  union ioctl_topic_info_args topic_info_args = {};
  topic_info_args.topic_name = {topic_name.c_str(), topic_name.size()};
  topic_info_args.topic_info_ret_buffer_addr = reinterpret_cast<uint64_t>(info_buffer.data());

  if (ioctl(agnocast_fd, AGNOCAST_GET_TOPIC_PUBLISHER_INFO_CMD, &topic_info_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_TOPIC_PUBLISHER_INFO_CMD failed: %s", strerror(errno));
    return false;
  }

  uint32_t publisher_count = topic_info_args.ret_topic_info_ret_num;

  for (uint32_t i = 0; i < publisher_count; ++i) {
    const auto & info = info_buffer[i];
    std::string name_to_add = info.node_name;

    if (!name_to_add.empty() && name_to_add[0] == '/') {
      name_to_add.erase(0, 1);
    }

    publisher_names.push_back(name_to_add);
  }

  return true;
}

}  // namespace agnocast
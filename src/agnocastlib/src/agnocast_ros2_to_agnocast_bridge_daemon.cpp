#include "agnocast/agnocast_ros2_to_agnocast_bridge_daemon.hpp"

#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <unistd.h>

#include <algorithm>
#include <functional>
#include <map>
#include <string>

namespace agnocast
{

std::map<std::string, BridgeSetupFunction> & get_bridge_factory_map()
{
  static std::map<std::string, BridgeSetupFunction> factory_map;
  return factory_map;
}

inline rclcpp::QoS parse_qos_from_args(int argc, char * argv[])
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

  if (argc < 3) {
    std::cerr << "Usage: " << argv[0] << " <topic_name> <message_type> [qos_options]" << std::endl;
    return EXIT_FAILURE;
  }

  std::string topic_name = argv[1];
  std::string message_type = argv[2];
  rclcpp::QoS qos = agnocast::parse_qos_from_args(argc, argv);

  std::string node_name_suffix = topic_name;
  std::replace(node_name_suffix.begin(), node_name_suffix.end(), '/', '_');

  rclcpp::init(0, nullptr);
  auto node = rclcpp::Node::make_shared("agnocast_bridge" + node_name_suffix);
  auto logger = node->get_logger();

  auto & factory = agnocast::get_bridge_factory_map();
  auto it = factory.find(message_type);

  if (it != factory.end()) {
    RCLCPP_INFO(logger, "Found bridge handler for type: %s", message_type.c_str());
    it->second(node, topic_name, qos);
  } else {
    RCLCPP_ERROR(logger, "No bridge handler registered for message type: %s", message_type.c_str());
    rclcpp::shutdown();
    return EXIT_FAILURE;
  }

  RCLCPP_INFO(logger, "Bridge daemon started for topic: %s", topic_name.c_str());
  rclcpp::spin(node);
  RCLCPP_INFO(logger, "Bridge daemon shutting down for topic: %s", topic_name.c_str());
  rclcpp::shutdown();

  return EXIT_SUCCESS;
}

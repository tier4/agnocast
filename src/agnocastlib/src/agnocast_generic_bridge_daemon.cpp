#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

#include <unistd.h>

#include <algorithm>
#include <functional>
#include <map>
#include <string>

// --- Include necessary ROS 2 message types ---
#include "sensor_msgs/msg/image.hpp"
#include "std_msgs/msg/int64.hpp"
#include "std_msgs/msg/string.hpp"

namespace agnocast
{
using BridgeSetupFunction =
  std::function<void(rclcpp::Node::SharedPtr, const std::string &, const rclcpp::QoS &)>;

std::map<std::string, BridgeSetupFunction> & get_bridge_factory_map()
{
  static std::map<std::string, BridgeSetupFunction> factory_map;
  return factory_map;
}

template <typename MessageT>
class BridgeRegistrar
{
public:
  BridgeRegistrar(const std::string & type_name)
  {
    get_bridge_factory_map()[type_name] = [type_name](
                                            rclcpp::Node::SharedPtr node,
                                            const std::string & topic_name,
                                            const rclcpp::QoS & qos) {
      auto logger = node->get_logger();
      RCLCPP_INFO(
        logger, "Setting up bridge for type %s on topic %s", type_name.c_str(), topic_name.c_str());

      agnocast::PublisherOptions pub_options;
      auto internal_agno_publisher =
        std::make_shared<agnocast::Publisher<MessageT>>(node.get(), topic_name, qos, pub_options);

      auto ros2_callback = [logger,
                            internal_agno_publisher](const typename MessageT::ConstSharedPtr msg) {
        RCLCPP_DEBUG(logger, "Bridging message from ROS 2 to Agnocast");
        auto loaned_msg = internal_agno_publisher->borrow_loaned_message();
        *loaned_msg = *msg;
        internal_agno_publisher->publish(std::move(loaned_msg));
      };

      rclcpp::SubscriptionOptions sub_options;
      sub_options.callback_group =
        node->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
      sub_options.ignore_local_publications = true;

      node->create_subscription<MessageT>(topic_name, qos, ros2_callback, sub_options);
    };
  }
};

// --- Register bridge handlers for common message types ---
static BridgeRegistrar<std_msgs::msg::String> string_registrar("std_msgs/msg/String");
static BridgeRegistrar<sensor_msgs::msg::Image> image_registrar("sensor_msgs/msg/Image");
static BridgeRegistrar<std_msgs::msg::Int64> int64_registrar("std_msgs/msg/Int64");

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

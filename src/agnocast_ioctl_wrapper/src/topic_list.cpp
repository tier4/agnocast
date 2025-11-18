#include "agnocast_ioctl.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <algorithm>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

namespace
{

bool is_service_topic(const std::string & topic_name)
{
  const std::string prefix = "/AGNOCAST_SRV_";
  if (topic_name.size() < prefix.size()) {
    return false;
  }
  return topic_name.compare(0, prefix.size(), prefix) == 0;
}

std::optional<std::vector<std::string>> get_agnocast_topics()
{
  int fd = open("/dev/agnocast", O_RDONLY);
  if (fd < 0) {
    if (errno == ENOENT) {
      fprintf(stderr,
        "Failed to open /dev/agnocast: Device not found. "
        "Please ensure the agnocast kernel module is installed and loaded. "
        "Run 'sudo modprobe agnocast' or 'sudo insmod <path-to-agnocast.ko>' to load the module.\n");
    } else {
      perror("Failed to open /dev/agnocast");
    }
    return std::nullopt;
  }

  std::array<char, MAX_TOPIC_NUM * TOPIC_NAME_BUFFER_SIZE> agnocast_topic_buffer{};

  ioctl_topic_list_args topic_list_args = {};
  topic_list_args.topic_name_buffer_addr = reinterpret_cast<uint64_t>(agnocast_topic_buffer.data());
  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    close(fd);
    return std::nullopt;
  }

  std::vector<std::string> agnocast_topics;
  agnocast_topics.reserve(topic_list_args.ret_topic_num);
  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    std::string topic_name = agnocast_topic_buffer.data() + i * TOPIC_NAME_BUFFER_SIZE;
    // Filter out topics used for service/client.
    if (!is_service_topic(topic_name)) {
      agnocast_topics.push_back(std::move(topic_name));
    }
  }

  close(fd);
  return agnocast_topics;
}

std::vector<std::string> get_ros2_topics()
{
  rclcpp::init(0, nullptr);
  auto node = rclcpp::Node::make_shared("agnocast_topic_list_all");

  // wait for ROS 2 to start
  constexpr std::chrono::milliseconds wait_time(200);
  std::this_thread::sleep_for(wait_time);

  auto ros2_topic_names_and_types = node->get_topic_names_and_types();
  std::vector<std::string> ros2_topics(ros2_topic_names_and_types.size());
  std::transform(
    ros2_topic_names_and_types.begin(), ros2_topic_names_and_types.end(), ros2_topics.begin(),
    [](const auto & pair) { return pair.first; });

  rclcpp::shutdown();
  return ros2_topics;
}

}  // namespace

extern "C" int topic_list()
{
  std::optional<std::vector<std::string>> agnocast_topics_opt = get_agnocast_topics();
  if (!agnocast_topics_opt.has_value()) {
    return -1;
  }
  std::vector<std::string> & agnocast_topics = agnocast_topics_opt.value();

  auto ros2_topics = get_ros2_topics();

  // ======== Print topics ========
  // Before printing, merge topics that exist in both vectors to avoid duplicates.

  std::sort(agnocast_topics.begin(), agnocast_topics.end());
  std::sort(ros2_topics.begin(), ros2_topics.end());

  size_t agnocast_topic_index = 0;
  size_t ros2_topic_index = 0;
  while (agnocast_topic_index < agnocast_topics.size() || ros2_topic_index < ros2_topics.size()) {
    if (agnocast_topic_index == agnocast_topics.size()) {
      for (size_t i = ros2_topic_index; i < ros2_topics.size(); i++) {
        std::cout << ros2_topics[i] << std::endl;
      }
      break;
    }

    if (ros2_topic_index == ros2_topics.size()) {
      for (size_t i = agnocast_topic_index; i < agnocast_topics.size(); i++) {
        std::cout << agnocast_topics[i] << " (Agnocast enabled)" << std::endl;
      }
      break;
    }

    int ret = agnocast_topics[agnocast_topic_index].compare(ros2_topics[ros2_topic_index]);
    if (ret == 0) {
      std::cout << agnocast_topics[agnocast_topic_index] << " (Agnocast enabled)" << std::endl;
      agnocast_topic_index++;
      ros2_topic_index++;
    } else if (ret < 0) {
      // This branch is executed when only Agnocast Subscription exists.
      std::cout << agnocast_topics[agnocast_topic_index] << " (Agnocast enabled)" << std::endl;
      agnocast_topic_index++;
    } else {
      std::cout << ros2_topics[ros2_topic_index] << std::endl;
      ros2_topic_index++;
    }
  }

  return 0;
}

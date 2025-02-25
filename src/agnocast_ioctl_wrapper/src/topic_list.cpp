#include "agnocast_ioctl.hpp"
#include "rclcpp/rclcpp.hpp"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <algorithm>
#include <iostream>
#include <string>
#include <vector>

extern "C" int topic_list()
{
  // ======== Get Agnocast topics ========

  int fd = open("/dev/agnocast", O_RDONLY);
  if (fd < 0) {
    perror("Failed to open /dev/agnocast");
    return -1;
  }

  char * agnocast_topic_buffer =
    static_cast<char *>(malloc(MAX_TOPIC_NUM * TOPIC_NAME_BUFFER_SIZE));

  union ioctl_topic_list_args topic_list_args = {};
  topic_list_args.topic_name_buffer_addr = reinterpret_cast<uint64_t>(agnocast_topic_buffer);
  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    free(agnocast_topic_buffer);
    close(fd);
    return -1;
  }

  std::vector<std::string> agnocast_topics(topic_list_args.ret_topic_num);
  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    agnocast_topics[i] = agnocast_topic_buffer + static_cast<size_t>(i) * TOPIC_NAME_BUFFER_SIZE;
  }

  std::sort(agnocast_topics.begin(), agnocast_topics.end());

  free(agnocast_topic_buffer);
  close(fd);

  // ======== Get ROS 2 topics ========

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

  std::sort(ros2_topics.begin(), ros2_topics.end());

  rclcpp::shutdown();

  // ======== Print topics ========

  int agnocast_topic_index = 0;
  int ros2_topic_index = 0;
  while (agnocast_topic_index < topic_list_args.ret_topic_num ||
         ros2_topic_index < ros2_topics.size()) {
    if (agnocast_topic_index == topic_list_args.ret_topic_num) {
      for (int i = ros2_topic_index; i < ros2_topics.size(); i++) {
        std::cout << ros2_topics[i] << std::endl;
      }
      break;
    }

    if (ros2_topic_index == ros2_topics.size()) {
      for (int i = agnocast_topic_index; i < topic_list_args.ret_topic_num; i++) {
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

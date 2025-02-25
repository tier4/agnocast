#pragma once

#include <cstdint>

#define MAX_TOPIC_NUM 1024
#define TOPIC_NAME_BUFFER_SIZE 256

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_topic_list_args {
  uint64_t topic_name_buffer_addr;
  uint32_t ret_topic_num;
};

union ioctl_node_info_args {
  struct
  {
    const char * node_name;
    uint64_t topic_name_buffer_addr;
  };
  uint32_t ret_topic_num;
};
#pragma GCC diagnostic pop

#define AGNOCAST_GET_TOPIC_LIST_CMD _IOR('R', 1, union ioctl_topic_list_args)
#define AGNOCAST_GET_NODE_SUBSCRIBER_TOPICS_CMD _IOR('R', 2, union ioctl_node_info_args)
#define AGNOCAST_GET_NODE_PUBLISHER_TOPICS_CMD _IOR('R', 3, union ioctl_node_info_args)

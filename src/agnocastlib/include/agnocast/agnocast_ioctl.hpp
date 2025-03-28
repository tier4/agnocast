#pragma once

#include <sys/ioctl.h>
#include <sys/types.h>

#include <cstdint>

namespace agnocast
{

#define MAX_PUBLISHER_NUM 4    // Maximum number of publishers per topic
#define MAX_SUBSCRIBER_NUM 16  // Maximum number of subscribers per topic
#define MAX_QOS_DEPTH 10       // Maximum QoS depth for each publisher/subscriber
#define MAX_RELEASE_NUM 3      // Maximum number of entries that can be released at one ioctl
#define VERSION_BUFFER_LEN 32  // Maximum size of version number represented as a string

using topic_local_id_t = int32_t;
struct publisher_shm_info
{
  uint32_t publisher_num;
  pid_t publisher_pids[MAX_PUBLISHER_NUM];
  uint64_t shm_addrs[MAX_PUBLISHER_NUM];
  uint64_t shm_sizes[MAX_PUBLISHER_NUM];
};
struct name_info
{
  const char * ptr;
  uint64_t len;
};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_subscriber_args {
  struct
  {
    struct name_info topic_name;
    struct name_info node_name;
    pid_t subscriber_pid;
    uint32_t qos_depth;
    bool qos_is_transient_local;
    bool is_take_sub;
  };
  struct
  {
    topic_local_id_t ret_id;
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_publisher_args {
  struct
  {
    struct name_info topic_name;
    struct name_info node_name;
    pid_t publisher_pid;
    uint32_t qos_depth;
    bool qos_is_transient_local;
  };
  struct
  {
    topic_local_id_t ret_id;
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
struct ioctl_update_entry_args
{
  struct name_info topic_name;
  topic_local_id_t pubsub_id;
  int64_t entry_id;
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_receive_msg_args {
  struct
  {
    struct name_info topic_name;
    topic_local_id_t subscriber_id;
  };
  struct
  {
    uint16_t ret_entry_num;
    int64_t ret_entry_ids[MAX_QOS_DEPTH];
    uint64_t ret_entry_addrs[MAX_QOS_DEPTH];
    struct publisher_shm_info ret_pub_shm_info;
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_publish_args {
  struct
  {
    struct name_info topic_name;
    topic_local_id_t publisher_id;
    uint64_t msg_virtual_address;
  };
  struct
  {
    int64_t ret_entry_id;
    uint32_t ret_subscriber_num;
    topic_local_id_t ret_subscriber_ids[MAX_SUBSCRIBER_NUM];
    uint32_t ret_released_num;
    uint64_t ret_released_addrs[MAX_RELEASE_NUM];
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_take_msg_args {
  struct
  {
    struct name_info topic_name;
    topic_local_id_t subscriber_id;
    bool allow_same_message;
  };
  struct
  {
    uint64_t ret_addr;
    int64_t ret_entry_id;
    struct publisher_shm_info ret_pub_shm_info;
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_new_shm_args {
  struct
  {
    pid_t pid;
    uint64_t shm_size;
  };
  uint64_t ret_addr;
};
#pragma GCC diagnostic pop

struct ioctl_get_version_args
{
  char ret_version[VERSION_BUFFER_LEN];
};

union ioctl_get_subscriber_num_args {
  struct name_info topic_name;
  uint32_t ret_subscriber_num;
};

#define AGNOCAST_SUBSCRIBER_ADD_CMD _IOWR(0xA6, 1, union ioctl_subscriber_args)
#define AGNOCAST_PUBLISHER_ADD_CMD _IOWR(0xA6, 2, union ioctl_publisher_args)
#define AGNOCAST_INCREMENT_RC_CMD _IOW(0xA6, 3, struct ioctl_update_entry_args)
#define AGNOCAST_DECREMENT_RC_CMD _IOW(0xA6, 4, struct ioctl_update_entry_args)
#define AGNOCAST_RECEIVE_MSG_CMD _IOWR(0xA6, 5, union ioctl_receive_msg_args)
#define AGNOCAST_PUBLISH_MSG_CMD _IOWR(0xA6, 6, union ioctl_publish_args)
#define AGNOCAST_TAKE_MSG_CMD _IOWR(0xA6, 7, union ioctl_take_msg_args)
#define AGNOCAST_NEW_SHM_CMD _IOWR(0xA6, 8, union ioctl_new_shm_args)
#define AGNOCAST_GET_VERSION_CMD _IOR(0xA6, 9, struct ioctl_get_version_args)
#define AGNOCAST_GET_SUBSCRIBER_NUM_CMD _IOWR(0xA6, 10, union ioctl_get_subscriber_num_args)

}  // namespace agnocast

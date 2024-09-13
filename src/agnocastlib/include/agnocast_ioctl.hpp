#pragma once

#include <sys/ioctl.h>

#include <cstdint>

namespace agnocast
{

// TODO: should be made larger when applied for Autoware
#define MAX_PUBLISHER_NUM 2   // At least 2 is required for sample application
#define MAX_SUBSCRIBER_NUM 8  // At least 6 is required for pointcloud topic in Autoware

#define MAX_QOS_DEPTH 10  // Maximum depth of transient local usage part in Autoware

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_subscriber_args {
  struct
  {
    const char * topic_name;
    uint32_t qos_depth;
    uint32_t subscriber_pid;
  };
  struct
  {
    uint32_t ret_transient_local_num;
    uint32_t ret_publisher_pids[MAX_QOS_DEPTH];
    uint64_t ret_timestamps[MAX_QOS_DEPTH];
    uint64_t ret_last_msg_addrs[MAX_QOS_DEPTH];
    uint32_t ret_publisher_num;
    uint32_t ret_pids[MAX_PUBLISHER_NUM];
    uint64_t ret_shm_addrs[MAX_PUBLISHER_NUM];
    uint64_t ret_shm_sizes[MAX_PUBLISHER_NUM];
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_publisher_args {
  struct
  {
    const char * topic_name;
    uint32_t publisher_pid;
  };
  struct
  {
    uint64_t ret_shm_addr;
    uint64_t ret_shm_size;
    uint32_t ret_subscriber_len;
    uint32_t ret_subscriber_pids[MAX_SUBSCRIBER_NUM];
  };
};
#pragma GCC diagnostic pop

#define MAX_RELEASE_NUM 3  // Max to keep union size equal to 32 bytes

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_enqueue_and_release_args {
  struct
  {
    const char * topic_name;
    uint32_t publisher_pid;
    uint32_t qos_depth;
    uint64_t msg_virtual_address;
    uint64_t timestamp;
  };
  struct
  {
    uint32_t ret_len;
    uint64_t ret_released_addrs[MAX_RELEASE_NUM];
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_update_entry_args {
  struct
  {
    const char * topic_name;
    uint32_t subscriber_pid;
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
  };
  uint64_t ret;
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_receive_msg_args {
  struct
  {
    const char * topic_name;
    uint32_t subscriber_pid;
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
    uint32_t qos_depth;
  };
  uint64_t ret;
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_publish_args {
  struct
  {
    const char * topic_name;
    uint32_t publisher_pid;
    uint64_t msg_timestamp;
  };
  struct
  {
    uint32_t ret_pids[MAX_SUBSCRIBER_NUM];
    uint32_t ret_len;
  };
};
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_new_shm_args {
  struct
  {
    uint32_t pid;
    uint64_t shm_size;
  };
  uint64_t ret_addr;
};
#pragma GCC diagnostic pop

union ioctl_get_subscriber_num_args {
  const char * topic_name;
  uint32_t ret_subscriber_num;
};

#define AGNOCAST_SUBSCRIBER_ADD_CMD _IOW('S', 1, union ioctl_subscriber_args)
#define AGNOCAST_PUBLISHER_ADD_CMD _IOW('P', 1, union ioctl_publisher_args)
#define AGNOCAST_ENQUEUE_AND_RELEASE_CMD _IOW('E', 1, union ioctl_enqueue_and_release_args)
#define AGNOCAST_INCREMENT_RC_CMD _IOW('M', 1, union ioctl_update_entry_args)
#define AGNOCAST_DECREMENT_RC_CMD _IOW('M', 2, union ioctl_update_entry_args)
#define AGNOCAST_RECEIVE_MSG_CMD _IOW('M', 3, union ioctl_receive_msg_args)
#define AGNOCAST_PUBLISH_MSG_CMD _IOW('M', 4, union ioctl_publish_args)
#define AGNOCAST_NEW_SHM_CMD _IOW('I', 1, union ioctl_new_shm_args)
#define AGNOCAST_GET_SUBSCRIBER_NUM_CMD _IOW('G', 1, union ioctl_get_subscriber_num_args)

}  // namespace agnocast

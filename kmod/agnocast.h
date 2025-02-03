#pragma once

#include <linux/types.h>

// TODO: should be made larger when applied for Autoware
#define MAX_PUBLISHER_NUM 4   // At least 4 is required for sample application
#define MAX_SUBSCRIBER_NUM 8  // At least 6 is required for pointcloud topic in Autoware

#define MAX_QOS_DEPTH 10  // Maximum depth of transient local usage part in Autoware

typedef int32_t topic_local_id_t;

union ioctl_subscriber_args {
  struct
  {
    const char * topic_name;
    uint32_t qos_depth;
    pid_t subscriber_pid;
    uint64_t init_timestamp;
    bool is_take_sub;
  };
  struct
  {
    topic_local_id_t ret_id;
    uint32_t ret_transient_local_num;
    uint64_t ret_timestamps[MAX_QOS_DEPTH];
    uint64_t ret_last_msg_addrs[MAX_QOS_DEPTH];
    uint32_t ret_publisher_num;
    pid_t ret_publisher_pids[MAX_PUBLISHER_NUM];
    uint64_t ret_shm_addrs[MAX_PUBLISHER_NUM];
    uint64_t ret_shm_sizes[MAX_PUBLISHER_NUM];
  };
};

union ioctl_publisher_args {
  struct
  {
    const char * topic_name;
    pid_t publisher_pid;
  };
  struct
  {
    topic_local_id_t ret_id;
    uint64_t ret_shm_addr;
    uint64_t ret_shm_size;
    uint32_t ret_subscriber_num;
    pid_t ret_subscriber_pids[MAX_SUBSCRIBER_NUM];
  };
};

#define MAX_RELEASE_NUM 3  // Max to keep union size equal to 32 bytes

union ioctl_enqueue_and_release_args {
  struct
  {
    const char * topic_name;
    topic_local_id_t publisher_id;
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

union ioctl_update_entry_args {
  struct
  {
    const char * topic_name;
    topic_local_id_t subscriber_id;
    uint64_t msg_timestamp;
  };
  uint64_t ret;
};

union ioctl_receive_msg_args {
  struct
  {
    const char * topic_name;
    topic_local_id_t subscriber_id;
    uint32_t qos_depth;
  };
  struct
  {
    uint16_t ret_len;
    uint64_t ret_timestamps[MAX_QOS_DEPTH];
    uint64_t ret_last_msg_addrs[MAX_QOS_DEPTH];
  };
};

union ioctl_publish_args {
  struct
  {
    const char * topic_name;
    topic_local_id_t publisher_id;
    uint64_t msg_timestamp;
  };
  struct
  {
    uint32_t ret_subscriber_num;
    topic_local_id_t ret_subscriber_ids[MAX_SUBSCRIBER_NUM];
  };
};

union ioctl_take_msg_args {
  struct
  {
    const char * topic_name;
    topic_local_id_t subscriber_id;
    uint32_t qos_depth;
    bool allow_same_message;
  };
  struct
  {
    uint64_t ret_addr;
    uint64_t ret_timestamp;
  };
};

union ioctl_new_shm_args {
  struct
  {
    pid_t pid;
    uint64_t shm_size;
  };
  uint64_t ret_addr;
};

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
#define AGNOCAST_TAKE_MSG_CMD _IOW('M', 5, union ioctl_take_msg_args)
#define AGNOCAST_NEW_SHM_CMD _IOW('I', 1, union ioctl_new_shm_args)
#define AGNOCAST_GET_SUBSCRIBER_NUM_CMD _IOW('G', 1, union ioctl_get_subscriber_num_args)

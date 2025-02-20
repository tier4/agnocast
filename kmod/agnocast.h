#pragma once

#include <linux/types.h>

// TODO: should be made larger when applied for Autoware
#define MAX_PUBLISHER_NUM 4   // At least 4 is required for sample application
#define MAX_SUBSCRIBER_NUM 8  // At least 6 is required for pointcloud topic in Autoware
#define MAX_QOS_DEPTH 10      // Maximum depth of transient local usage part in Autoware
#define MAX_RELEASE_NUM 3     // Max to keep union size equal to 32 bytes
#define MAX_MAP_NUM 8         // Max number of read-only shared memory regions mappable per process

typedef int32_t topic_local_id_t;
struct publisher_shm_info
{
  uint32_t publisher_num;
  pid_t publisher_pids[MAX_PUBLISHER_NUM];
  uint64_t shm_addrs[MAX_PUBLISHER_NUM];
  uint64_t shm_sizes[MAX_PUBLISHER_NUM];
};

union ioctl_subscriber_args {
  struct
  {
    const char * topic_name;
    uint32_t qos_depth;
    pid_t subscriber_pid;
    bool is_take_sub;
  };
  struct
  {
    topic_local_id_t ret_id;
    uint32_t ret_transient_local_num;
    int64_t ret_entry_ids[MAX_QOS_DEPTH];
    uint64_t ret_entry_addrs[MAX_QOS_DEPTH];
    struct publisher_shm_info ret_pub_shm_info;
  };
};

union ioctl_publisher_args {
  struct
  {
    const char * topic_name;
    pid_t publisher_pid;
    uint32_t qos_depth;
    bool qos_is_transient_local;
  };
  struct
  {
    topic_local_id_t ret_id;
  };
};

struct ioctl_update_entry_args
{
  const char * topic_name;
  topic_local_id_t pubsub_id;
  int64_t entry_id;
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
    uint16_t ret_entry_num;
    int64_t ret_entry_ids[MAX_QOS_DEPTH];
    uint64_t ret_entry_addrs[MAX_QOS_DEPTH];
    struct publisher_shm_info ret_pub_shm_info;
  };
};

union ioctl_publish_args {
  struct
  {
    const char * topic_name;
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
    int64_t ret_entry_id;
    struct publisher_shm_info ret_pub_shm_info;
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
#define AGNOCAST_INCREMENT_RC_CMD _IOW('M', 1, struct ioctl_update_entry_args)
#define AGNOCAST_DECREMENT_RC_CMD _IOW('M', 2, struct ioctl_update_entry_args)
#define AGNOCAST_RECEIVE_MSG_CMD _IOW('M', 3, union ioctl_receive_msg_args)
#define AGNOCAST_PUBLISH_MSG_CMD _IOW('M', 4, union ioctl_publish_args)
#define AGNOCAST_TAKE_MSG_CMD _IOW('M', 5, union ioctl_take_msg_args)
#define AGNOCAST_NEW_SHM_CMD _IOW('I', 1, union ioctl_new_shm_args)
#define AGNOCAST_GET_SUBSCRIBER_NUM_CMD _IOW('G', 1, union ioctl_get_subscriber_num_args)

// ================================================
// ros2cli ioctls

#define MAX_TOPIC_NUM 1024

union ioctl_topic_list_args {
  uint64_t topic_name_buffer_addr;
  uint32_t ret_topic_num;
};

#define AGNOCAST_GET_TOPIC_LIST_CMD _IOR('R', 1, union ioctl_topic_list_args)

// ================================================

void agnocast_init_mutexes(void);
int agnocast_init_sysfs(void);
void agnocast_init_device(void);
int agnocast_init_kthread(void);
int agnocast_init_kprobe(void);

void agnocast_exit_free_data(void);
void agnocast_exit_sysfs(void);
void agnocast_exit_kthread(void);
void agnocast_exit_kprobe(void);
void agnocast_exit_device(void);

int subscriber_add(
  char * topic_name, uint32_t qos_depth, const pid_t subscriber_pid, bool is_take_sub,
  union ioctl_subscriber_args * ioctl_ret);

int get_subscriber_num(char * topic_name, union ioctl_get_subscriber_num_args * ioctl_ret);

int new_shm_addr(const pid_t pid, uint64_t shm_size, union ioctl_new_shm_args * ioctl_ret);

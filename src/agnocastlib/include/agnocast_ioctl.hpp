#pragma once

#include <sys/ioctl.h>

namespace agnocast {

struct ioctl_subscriber_args {
    const char *topic_name;
    uint32_t pid;
};

struct ioctl_publisher_args {
    const char *topic_name;
    uint32_t pid;
};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_release_oldest_args {
    struct {
        const char *topic_name;
        uint32_t publisher_pid;
        uint32_t buffer_depth;
    };
    uint64_t ret;
};
#pragma GCC diagnostic pop

struct ioctl_enqueue_entry_args {
    const char *topic_name;
    uint32_t publisher_pid;
    uint64_t msg_virtual_address;
    uint64_t timestamp;
};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_update_entry_args {
    struct {
        const char *topic_name;
        uint32_t publisher_pid;
        uint64_t msg_timestamp;
    };
    uint64_t ret;
};
#pragma GCC diagnostic pop

#define MAX_SUBSCRIBER_NUM 16

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_publish_args {
    struct {
        const char *topic_name;
        uint32_t publisher_pid;
        uint64_t msg_timestamp;
    };
    struct {
        uint32_t ret_pids[MAX_SUBSCRIBER_NUM];
        uint32_t ret_len;
    };
};
#pragma GCC diagnostic pop

union ioctl_new_shm_args {
    uint32_t pid;
    uint64_t ret_addr;
};

#define MAX_PUBLISHER_NUM 16  // TODO: should be reconsidered

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_get_shm_args {
    const char *topic_name;
    struct {
        uint32_t ret_publisher_num;
        uint32_t ret_pids[MAX_PUBLISHER_NUM];
        uint64_t ret_addrs[MAX_PUBLISHER_NUM];
    };
};
#pragma GCC diagnostic pop

#define AGNOCAST_TOPIC_ADD_CMD _IOW('T', 1, char *)
#define AGNOCAST_SUBSCRIBER_ADD_CMD _IOW('S', 1, struct ioctl_subscriber_args)
#define AGNOCAST_SUBSCRIBER_REMOVE_CMD _IOW('S', 2, struct ioctl_subscriber_args)
#define AGNOCAST_PUBLISHER_ADD_CMD _IOW('P', 1, struct ioctl_publisher_args)
#define AGNOCAST_PUBLISHER_REMOVE_CMD _IOW('P', 2, struct ioctl_publisher_args)
#define AGNOCAST_RELEASE_OLDEST_CMD _IOW('P', 3, union ioctl_release_oldest_args)
#define AGNOCAST_ENQUEUE_ENTRY_CMD _IOW('E', 1, struct ioctl_enqueue_entry_args)
#define AGNOCAST_INCREMENT_RC_CMD _IOW('M', 1, union ioctl_update_entry_args)
#define AGNOCAST_DECREMENT_RC_CMD _IOW('M', 2, union ioctl_update_entry_args)
#define AGNOCAST_RECEIVE_MSG_CMD _IOW('M', 3, union ioctl_update_entry_args)
#define AGNOCAST_PUBLISH_MSG_CMD _IOW('M', 4, union ioctl_publish_args)
#define AGNOCAST_NEW_SHM_CMD _IOW('I', 1, union ioctl_new_shm_args)
#define AGNOCAST_GET_SHM_CMD _IOW('I', 2, union ioctl_get_shm_args)

} // namespace agnocast

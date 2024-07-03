#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>

#include <cerrno>
#include <cstdint>
#include <iostream>

struct ioctl_subscriber_args {
    char *topic_name;
    uint32_t pid;
};

struct ioctl_publisher_args {
    char *topic_name;
    uint32_t pid;
};

union ioctl_release_oldest_args {
    struct {
        char *topic_name;
        uint32_t publisher_pid;
        uint32_t buffer_depth;
    };
    uint64_t ret;
};

struct ioctl_enqueue_entry_args {
    char *topic_name;
    uint32_t publisher_pid;
    uint64_t msg_virtual_address;
    uint64_t timestamp;
};

union ioctl_update_entry_args {
    struct {
        char *topic_name;
        uint32_t publisher_pid;
        uint64_t msg_timestamp;
    };
    uint64_t ret;
};

#define MAX_SUBSCRIBER_NUM 16

union ioctl_publish_args {
    struct {
        char *topic_name;
        uint32_t publisher_pid;
        uint64_t msg_timestamp;
    };
    struct {
        uint32_t ret_pids[MAX_SUBSCRIBER_NUM];
        uint32_t ret_len;
    };
};

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

int main(int argc, char **argv) {
    int fd;
    char *key = "myKey1234";

    fd = open("/dev/agnocast", O_RDWR);
    if (fd < 0) {
        perror("Failed to open the device");
        return errno;
    }

    if (ioctl(fd, AGNOCAST_TOPIC_ADD_CMD, key) < 0) {
        perror("Failed to execute ioctl");
        close(fd);
        return errno;
    }

    struct ioctl_subscriber_args args;
    args.pid = 1234;
    args.topic_name = key;
    if (ioctl(fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &args) < 0) {
        perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
        close(fd);
        return errno;
    }

    args.pid = 1235;
    if (ioctl(fd, AGNOCAST_SUBSCRIBER_ADD_CMD, &args) < 0) {
        perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
        close(fd);
        return errno;
    }

    /*
    args.pid = 1234;
    if (ioctl(fd, AGNOCAST_SUBSCRIBER_REMOVE_CMD, &args) < 0) {
        perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
        close(fd);
        return errno;
    }
    */

    struct ioctl_publisher_args pub_args;
    pub_args.pid = 1;
    pub_args.topic_name = key;
     if (ioctl(fd, AGNOCAST_PUBLISHER_ADD_CMD, &pub_args) < 0) {
        perror("AGNOCAST_SUBSCRIBER_ADD_CMD failed");
        close(fd);
        return errno;
    }

    pub_args.pid = 2;
     if (ioctl(fd, AGNOCAST_PUBLISHER_ADD_CMD, &pub_args) < 0) {
        perror("AGNOCAST_PUBLISHER_ADD_CMD failed");
        close(fd);
        return errno;
    }

    /*
    pub_args.pid = 1;
    if (ioctl(fd, AGNOCAST_PUBLISHER_REMOVE_CMD, &pub_args) < 0) {
        perror("AGNOCAST_PUBLISHER_REMOVE_CMD failed");
        close(fd);
        return errno;
    }
    */

    struct ioctl_enqueue_entry_args enqueue_args;
    enqueue_args.topic_name = key;
    enqueue_args.publisher_pid = 2;
    enqueue_args.msg_virtual_address = 0xdeadbeef;
    enqueue_args.timestamp = 777777;
    if (ioctl(fd, AGNOCAST_ENQUEUE_ENTRY_CMD, &enqueue_args) < 0) {
        perror("AGNOCAST_ENQUEUE_ENTRY_CMD failed");
        close(fd);
        return errno;
    }

    enqueue_args.msg_virtual_address = 0xdeadbeef + 1;
    enqueue_args.timestamp = 777777 + 1;
    if (ioctl(fd, AGNOCAST_ENQUEUE_ENTRY_CMD, &enqueue_args) < 0) {
        perror("AGNOCAST_ENQUEUE_ENTRY_CMD failed");
        close(fd);
        return errno;
    }

    enqueue_args.msg_virtual_address = 0xdeadbeef + 2;
    enqueue_args.timestamp = 777777 + 2;
    if (ioctl(fd, AGNOCAST_ENQUEUE_ENTRY_CMD, &enqueue_args) < 0) {
        perror("AGNOCAST_ENQUEUE_ENTRY_CMD failed");
        close(fd);
        return errno;
    }

    union ioctl_update_entry_args entry_args;
    entry_args.topic_name = key;
    entry_args.publisher_pid = 2;
    entry_args.msg_timestamp = 777777 + 1;
    if (ioctl(fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_INCREMENT_RC_CMD failed");
        close(fd);
        return errno;
    }

    if (ioctl(fd, AGNOCAST_INCREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_INCREMENT_RC_CMD failed");
        close(fd);
        return errno;
    }

    if (ioctl(fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_DECREMENT_RC_CMD failed");
        close(fd);
        return errno;
    }

    union ioctl_publish_args publish_args;
    publish_args.topic_name = key;
    publish_args.publisher_pid = 2;
    publish_args.msg_timestamp = 777777;
    if (ioctl(fd, AGNOCAST_PUBLISH_MSG_CMD, &publish_args) < 0) {
        perror("AGNOCAST_PUBLISH_MSG_CMD failed");
        close(fd);
        return errno;
    }

    std::cout << "subscriber pids:" << std::endl;
    for (int i = 0; i < publish_args.ret_len; i++) {
        std::cout << publish_args.ret_pids[i] << " ";
    }
    std::cout << std::endl;

    entry_args.topic_name = key;
    entry_args.publisher_pid = 2;
    entry_args.msg_timestamp = 777777;
    if (ioctl(fd, AGNOCAST_RECEIVE_MSG_CMD, &entry_args) < 0) {
        perror("AGNOCAST_RECEIVE_MSG_CMD failed");
        close(fd);
        return errno;
    }

    std::cout << "received message with address=" << entry_args.ret << std::endl;

    entry_args.topic_name = key;
    entry_args.publisher_pid = 2;
    entry_args.msg_timestamp = 777777;
    if (ioctl(fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_DECREMENT_RC_CMD failed");
        close(fd);
        return errno;
    }

    entry_args.topic_name = key;
    entry_args.publisher_pid = 2;
    entry_args.msg_timestamp = 777777;
    if (ioctl(fd, AGNOCAST_RECEIVE_MSG_CMD, &entry_args) < 0) {
        perror("AGNOCAST_RECEIVE_MSG_CMD failed");
        close(fd);
        return errno;
    }

    std::cout << "received message with address=" << entry_args.ret << std::endl;

    entry_args.topic_name = key;
    entry_args.publisher_pid = 2;
    entry_args.msg_timestamp = 777777;
    if (ioctl(fd, AGNOCAST_DECREMENT_RC_CMD, &entry_args) < 0) {
        perror("AGNOCAST_DECREMENT_RC_CMD failed");
        close(fd);
        return errno;
    }

    union ioctl_release_oldest_args release_args;
    release_args.topic_name = key;
    release_args.publisher_pid = 2;
    release_args.buffer_depth = 1;
    if (ioctl(fd, AGNOCAST_RELEASE_OLDEST_CMD, &release_args) < 0) {
        perror("AGNOCAST_RELEASE_OLDEST_CMD failed");
        close(fd);
        return errno;
    }

    std::cout << "release message with address=" << release_args.ret << std::endl;

    close(fd);
    return 0;
}

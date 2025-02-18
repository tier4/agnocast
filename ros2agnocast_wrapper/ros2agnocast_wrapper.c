#include "ros2agnocast_wrapper.h"

#include <fcntl.h>
#include <stdio.h>
#include <sys/ioctl.h>
#include <unistd.h>

int topic_list()
{
  int fd = open("/dev/agnocast", O_RDWR);
  if (fd < 0) {
    perror("Failed to open the device");
    return -1;
  }

  struct ioctl_topic_list_args topic_list_args;
  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    close(fd);
    return -1;
  }

  close(fd);

  printf("TODO: list Agnocast topics\n");

  return 0;
}

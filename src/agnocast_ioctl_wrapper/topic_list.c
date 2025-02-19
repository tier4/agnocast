#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <unistd.h>

// ================================================
// ioctl definition: copy from kmod/agnocast.h

#define MAX_TOPIC_NUM 64

struct ioctl_topic_list_args
{
  uint32_t ret_topic_num;
  char * ret_topic_name[MAX_TOPIC_NUM];
};

#define AGNOCAST_GET_TOPIC_LIST_CMD _IOR('R', 1, struct ioctl_topic_list_args)

// ================================================

#define MAX_TOPIC_NAME_LEN 256

int topic_list()
{
  int fd = open("/dev/agnocast", O_RDWR);
  if (fd < 0) {
    perror("Failed to open /dev/agnocast");
    return -1;
  }

  struct ioctl_topic_list_args topic_list_args;
  for (int i = 0; i < MAX_TOPIC_NUM; i++) {
    topic_list_args.ret_topic_name[i] = malloc(MAX_TOPIC_NAME_LEN);
    if (topic_list_args.ret_topic_name[i] == NULL) {
      perror("Failed to allocate memory");
      for (int j = 0; j < i; j++) {
        free(topic_list_args.ret_topic_name[j]);
      }
      close(fd);
      return -1;
    }
  }

  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    for (int i = 0; i < MAX_TOPIC_NUM; i++) {
      free(topic_list_args.ret_topic_name[i]);
    }
    close(fd);
    return -1;
  }

  // bubble sort
  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    for (uint32_t j = 0; j < topic_list_args.ret_topic_num - 1; j++) {
      if (strcmp(topic_list_args.ret_topic_name[j], topic_list_args.ret_topic_name[j + 1]) > 0) {
        char * temp = topic_list_args.ret_topic_name[j];
        topic_list_args.ret_topic_name[j] = topic_list_args.ret_topic_name[j + 1];
        topic_list_args.ret_topic_name[j + 1] = temp;
      }
    }
  }

  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    printf("%s\n", topic_list_args.ret_topic_name[i]);
  }

  for (int i = 0; i < MAX_TOPIC_NUM; i++) {
    free(topic_list_args.ret_topic_name[i]);
  }

  close(fd);

  return 0;
}

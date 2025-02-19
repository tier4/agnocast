#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <algorithm>
#include <iostream>
#include <string>
#include <vector>

// ================================================
// ioctl definition: copy from kmod/agnocast.h

#define MAX_TOPIC_NUM 1024
#define TOPIC_NAME_BUFFER_SIZE 256

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
union ioctl_topic_list_args {
  uint64_t topic_name_buffer_addr;
  uint32_t ret_topic_num;
};
#pragma GCC diagnostic pop

#define AGNOCAST_GET_TOPIC_LIST_CMD _IOR('R', 1, union ioctl_topic_list_args)

// ================================================

extern "C" int topic_list()
{
  int fd = open("/dev/agnocast", O_RDONLY);
  if (fd < 0) {
    perror("Failed to open /dev/agnocast");
    return -1;
  }

  char * topic_name_buffer = static_cast<char *>(malloc(MAX_TOPIC_NUM * TOPIC_NAME_BUFFER_SIZE));

  union ioctl_topic_list_args topic_list_args = {};
  topic_list_args.topic_name_buffer_addr = reinterpret_cast<uint64_t>(topic_name_buffer);
  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    free(topic_name_buffer);
    close(fd);
    return -1;
  }

  std::vector<std::string> topic_names;
  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    topic_names.push_back(topic_name_buffer + i * TOPIC_NAME_BUFFER_SIZE);
  }

  std::sort(topic_names.begin(), topic_names.end());

  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    std::cout << topic_names[i] << std::endl;
  }

  free(topic_name_buffer);
  close(fd);

  return 0;
}

#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <algorithm>
#include <cstring>
#include <iostream>
#include <memory>
#include <vector>

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

extern "C" int topic_list()
{
  int fd = open("/dev/agnocast", O_RDONLY);
  if (fd < 0) {
    perror("Failed to open /dev/agnocast");
    return -1;
  }

  struct ioctl_topic_list_args topic_list_args = {};
  std::vector<std::unique_ptr<char[]>> buffers;
  buffers.reserve(MAX_TOPIC_NUM);
  constexpr size_t MAX_TOPIC_NAME_LEN = 256;
  for (auto & topic_name : topic_list_args.ret_topic_name) {
    buffers.push_back(std::make_unique<char[]>(MAX_TOPIC_NAME_LEN));
    topic_name = buffers.back().get();
  }

  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    close(fd);
    return -1;
  }

  std::sort(
    buffers.begin(), buffers.begin() + topic_list_args.ret_topic_num,
    [](const std::unique_ptr<char[]> & a, const std::unique_ptr<char[]> & b) {
      return std::strcmp(a.get(), b.get()) < 0;
    });

  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    std::cout << buffers[i].get() << std::endl;
  }

  close(fd);

  return 0;
}

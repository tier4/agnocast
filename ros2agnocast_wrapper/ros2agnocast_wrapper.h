#include <stdint.h>

struct ioctl_topic_list_args
{
  uint32_t dummy;
};

#define AGNOCAST_GET_TOPIC_LIST_CMD _IOR('R', 1, struct ioctl_topic_list_args)

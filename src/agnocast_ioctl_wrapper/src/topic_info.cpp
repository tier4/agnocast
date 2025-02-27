#include "agnocast_ioctl.hpp"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

extern "C" {

char ** get_agnocast_topic_list(int * topic_count)
{
  *topic_count = 0;

  int fd = open("/dev/agnocast", O_RDONLY);
  if (fd < 0) {
    perror("Failed to open /dev/agnocast");
    return nullptr;
  }

  char * agnocast_topic_buffer =
    static_cast<char *>(malloc(MAX_TOPIC_NUM * TOPIC_NAME_BUFFER_SIZE));

  union ioctl_topic_list_args topic_list_args = {};
  topic_list_args.topic_name_buffer_addr = reinterpret_cast<uint64_t>(agnocast_topic_buffer);
  if (ioctl(fd, AGNOCAST_GET_TOPIC_LIST_CMD, &topic_list_args) < 0) {
    perror("AGNOCAST_GET_TOPIC_LIST_CMD failed");
    free(agnocast_topic_buffer);
    close(fd);
    return nullptr;
  }

  std::vector<std::string> agnocast_topics(topic_list_args.ret_topic_num);
  for (uint32_t i = 0; i < topic_list_args.ret_topic_num; i++) {
    agnocast_topics[i] = agnocast_topic_buffer + static_cast<size_t>(i) * TOPIC_NAME_BUFFER_SIZE;
  }

  *topic_count = static_cast<int>(topic_list_args.ret_topic_num);

  free(agnocast_topic_buffer);
  close(fd);

  char ** topic_array = static_cast<char **>(malloc(*topic_count * sizeof(char *)));
  if (topic_array == nullptr) {
    return nullptr;
  }

  for (size_t i = 0; i < *topic_count; i++) {
    topic_array[i] = static_cast<char *>(malloc((agnocast_topics[i].size() + 1) * sizeof(char)));
    if (!topic_array[i]) {
      for (size_t j = 0; j < i; j++) {
        free(topic_array[j]);
      }
      free(topic_array);
      return nullptr;
    }
    std::strcpy(topic_array[i], agnocast_topics[i].c_str());
  }
  return topic_array;
}

struct topic_info_ret * get_agnocast_sub_nodes(const char * topic_name, int * topic_info_ret_count)
{
  *topic_info_ret_count = 0;

  struct topic_info_ret * agnocast_topic_info_ret_buffer =
    (struct topic_info_ret *)(malloc(MAX_TOPIC_INFO_RET_NUM * sizeof(struct topic_info_ret)));

  if (agnocast_topic_info_ret_buffer == nullptr) {
    fprintf(stderr, "Memory allocation failed\n");
    return nullptr;
  }

  ////FIXME: Replace this code to calling agnocast ////
  const char * nodes[] = {"/listener_node", "/tmp/node_B", "/tmp/temporary/node_C"};
  size_t num_nodes = 3;

  for (size_t i = 0; i < num_nodes; i++) {
    strncpy(
      agnocast_topic_info_ret_buffer[i].node_name, nodes[i],
      sizeof(agnocast_topic_info_ret_buffer[i].node_name) - 1);
    agnocast_topic_info_ret_buffer[i]
      .node_name[sizeof(agnocast_topic_info_ret_buffer[i].node_name) - 1] = '\0';
    agnocast_topic_info_ret_buffer[i].qos_depth = 3;
    agnocast_topic_info_ret_buffer[i].qos_is_transient_local = true;
  }
  ////////////////////////////////////////////////////

  *topic_info_ret_count = static_cast<int>(num_nodes);
  return agnocast_topic_info_ret_buffer;
}

struct topic_info_ret * get_agnocast_pub_nodes(const char * topic_name, int * topic_info_ret_count)
{
  *topic_info_ret_count = 0;

  struct topic_info_ret * agnocast_topic_info_ret_buffer =
    (struct topic_info_ret *)(malloc(MAX_TOPIC_INFO_RET_NUM * sizeof(struct topic_info_ret)));

  if (agnocast_topic_info_ret_buffer == nullptr) {
    fprintf(stderr, "Memory allocation failed\n");
    return nullptr;
  }

  ////FIXME: Replace this code to calling agnocast ////
  const char * nodes[] = {"/talker_node", "/tmp/node_B", "/tmp/temporary/node_C"};
  size_t num_nodes = 3;

  for (size_t i = 0; i < num_nodes; i++) {
    strncpy(
      agnocast_topic_info_ret_buffer[i].node_name, nodes[i],
      sizeof(agnocast_topic_info_ret_buffer[i].node_name) - 1);
    agnocast_topic_info_ret_buffer[i]
      .node_name[sizeof(agnocast_topic_info_ret_buffer[i].node_name) - 1] = '\0';
    agnocast_topic_info_ret_buffer[i].qos_depth = 3;
    agnocast_topic_info_ret_buffer[i].qos_is_transient_local = true;
  }
  ////////////////////////////////////////////////////

  *topic_info_ret_count = static_cast<int>(num_nodes);
  return agnocast_topic_info_ret_buffer;
}

void free_agnocast_topic_info_ret(struct topic_info_ret * array, int count)
{
  if (array == nullptr) {
    return;
  }

  free(array);
}
}

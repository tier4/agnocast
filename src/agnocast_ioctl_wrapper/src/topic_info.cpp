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

char ** get_agnocast_sub_nodes(const char * topic_name, int * node_count)
{
  *node_count = 0;

  char * agnocast_node_buffer = static_cast<char *>(malloc(MAX_NODE_NUM * NODE_NAME_BUFFER_SIZE));

  if (agnocast_node_buffer == nullptr) {
    fprintf(stderr, "Memory allocation failed\n");
    return nullptr;
  }

  ////FIXME: Replace this code to calling agnocast ////
  const char * nodes[] = {"/my_topic", "/tmp/node_B", "/tmp/temporary/node_C"};
  size_t num_nodes = sizeof(nodes) / sizeof(nodes[0]);

  for (size_t i = 0; i < num_nodes; i++) {
    strncpy(
      agnocast_node_buffer + (i * NODE_NAME_BUFFER_SIZE), nodes[i], NODE_NAME_BUFFER_SIZE - 1);
    agnocast_node_buffer[(i + 1) * NODE_NAME_BUFFER_SIZE - 1] = '\0';
  }

  *node_count = static_cast<int>(num_nodes);

  std::vector<std::string> agnocast_sub_nodes(*node_count);
  for (uint32_t i = 0; i < *node_count; i++) {
    agnocast_sub_nodes[i] = agnocast_node_buffer + static_cast<size_t>(i) * NODE_NAME_BUFFER_SIZE;
  }

  free(agnocast_node_buffer);
  ////////////////////////////////////////////////////

  char ** node_array = static_cast<char **>(malloc(*node_count * sizeof(char *)));
  if (node_array == nullptr) {
    return nullptr;
  }

  for (size_t i = 0; i < *node_count; i++) {
    node_array[i] = static_cast<char *>(malloc((agnocast_sub_nodes[i].size() + 1) * sizeof(char)));
    if (!node_array[i]) {
      for (size_t j = 0; j < i; j++) {
        free(node_array[j]);
      }
      free(node_array);
      return nullptr;
    }
    std::strcpy(node_array[i], agnocast_sub_nodes[i].c_str());
  }
  return node_array;
}

char ** get_agnocast_pub_nodes(const char * topic_name, int * node_count)
{
  *node_count = 0;

  char * agnocast_node_buffer = static_cast<char *>(malloc(MAX_NODE_NUM * NODE_NAME_BUFFER_SIZE));

  if (agnocast_node_buffer == nullptr) {
    fprintf(stderr, "Memory allocation failed\n");
    return nullptr;
  }
  ////FIXME: Replace this code to calling agnocast ////
  const char * nodes[] = {"/my_topic", "/tmp/node_B", "/tmp/temporary/node_C"};
  size_t num_nodes = sizeof(nodes) / sizeof(nodes[0]);

  for (size_t i = 0; i < num_nodes; i++) {
    strncpy(
      agnocast_node_buffer + (i * NODE_NAME_BUFFER_SIZE), nodes[i], NODE_NAME_BUFFER_SIZE - 1);
    agnocast_node_buffer[(i + 1) * NODE_NAME_BUFFER_SIZE - 1] = '\0';
  }

  *node_count = static_cast<int>(num_nodes);

  std::vector<std::string> agnocast_pub_nodes(*node_count);
  for (uint32_t i = 0; i < *node_count; i++) {
    agnocast_pub_nodes[i] = agnocast_node_buffer + static_cast<size_t>(i) * NODE_NAME_BUFFER_SIZE;
  }

  free(agnocast_node_buffer);
  ////////////////////////////////////////////////////
  char ** node_array = static_cast<char **>(malloc(*node_count * sizeof(char *)));
  if (node_array == nullptr) {
    return nullptr;
  }

  for (size_t i = 0; i < *node_count; i++) {
    node_array[i] = static_cast<char *>(malloc((agnocast_pub_nodes[i].size() + 1) * sizeof(char)));
    if (!node_array[i]) {
      for (size_t j = 0; j < i; j++) {
        free(node_array[j]);
      }
      free(node_array);
      return nullptr;
    }
    std::strcpy(node_array[i], agnocast_pub_nodes[i].c_str());
  }
  return node_array;
}

void free_agnocast_nodes_and_topics(char ** array, int count)
{
  if (array == nullptr) {
    return;
  }

  for (int i = 0; i < count; i++) {
    free(array[i]);
  }
  free(array);
}
}

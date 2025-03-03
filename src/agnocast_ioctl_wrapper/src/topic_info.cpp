#include "agnocast_ioctl.hpp"

#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

extern "C" {

struct topic_info_ret * get_agnocast_sub_nodes(const char * topic_name, int * topic_info_ret_count)
{
  *topic_info_ret_count = 0;

  struct topic_info_ret * agnocast_topic_info_ret_buffer = static_cast<struct topic_info_ret *>(
    malloc(MAX_TOPIC_INFO_RET_NUM * sizeof(struct topic_info_ret)));

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

  struct topic_info_ret * agnocast_topic_info_ret_buffer = static_cast<struct topic_info_ret *>(
    malloc(MAX_TOPIC_INFO_RET_NUM * sizeof(struct topic_info_ret)));

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
  free(array);
}
}

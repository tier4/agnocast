
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

extern "C" {

char ** get_agnocast_sub_topics(const char * node_name, int * topic_count)
{
  (void)node_name;
  ///////////////////////////////////////
  // This is a dummy implementation
  // In a real implementation, you should get the list of topics from agnocast
  // TODO(TetsuKawa): Implement the real implementation
  ///////////////////////////////////////
  std::vector<std::string> topics = {
    "/chatter",
    "/another_topic_sub",
  };
  ///////////////////////////////////////

  *topic_count = 2;

  char ** topic_array = static_cast<char **>(malloc(*topic_count * sizeof(char *)));
  if (!topic_array) {
    return nullptr;
  }

  for (size_t i = 0; i < *topic_count; i++) {
    topic_array[i] = static_cast<char *>(malloc((topics[i].size() + 1) * sizeof(char)));
    if (!topic_array[i]) {
      for (size_t j = 0; j < i; j++) {
        free(topic_array[j]);
      }
      free(topic_array);
      return nullptr;
    }
    std::strcpy(topic_array[i], topics[i].c_str());
  }
  return topic_array;
}

char ** get_agnocast_pub_topics(const char * node_name, int * topic_count)
{
  (void)node_name;
  ///////////////////////////////////////
  // This is a dummy implementation
  // In a real implementation, you should get the list of topics from agnocast
  // TODO(TetsuKawa): Implement the real implementation
  ///////////////////////////////////////
  std::vector<std::string> topics = {
    "/chatter",
    "/another_topic_pub",
  };
  ///////////////////////////////////////

  *topic_count = 2;

  char ** topic_array = static_cast<char **>(malloc(*topic_count * sizeof(char *)));  // NOLINT
  if (!topic_array) {
    return nullptr;
  }

  for (size_t i = 0; i < *topic_count; i++) {
    topic_array[i] = static_cast<char *>(malloc((topics[i].size() + 1) * sizeof(char)));  // NOLINT
    if (!topic_array[i]) {
      for (size_t j = 0; j < i; j++) {
        free(topic_array[j]);  // NOLINT
      }
      free(topic_array);  // NOLINT
      return nullptr;
    }
    std::strcpy(topic_array[i], topics[i].c_str());  // NOLINT
  }
  return topic_array;
}

void free_agnocast_topics(char ** topic_array, int topic_count)
{
  if (!topic_array) {
    return;
  }

  for (int i = 0; i < topic_count; i++) {
    free(topic_array[i]);  // NOLINT
  }
  free(topic_array);  // NOLINT
}
}
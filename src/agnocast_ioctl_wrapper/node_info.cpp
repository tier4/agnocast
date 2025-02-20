
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

extern "C" {

char ** get_agnocast_sub_topics(const char * node_name, int * topic_count)
{
  ///////////////////////////////////////
  // This is a dummy implementation
  // In a real implementation, you should get the list of topics from agnocast
  // TODO(TetsuKawa): Implement the real implementation
  ///////////////////////////////////////
  (void *)node_name;
  std::vector<std::string> topics = {
    "/chatter",
    "/another_topic_sub",
  };
  ///////////////////////////////////////

  *topic_count = topics.size();

  char ** topic_array = (char **)malloc(topics.size() * sizeof(char *));
  for (size_t i = 0; i < topics.size(); i++) {
    topic_array[i] = strdup(topics[i].c_str());
  }
  return topic_array;
}

char ** get_agnocast_pub_topics(const char * node_name, int * topic_count)
{
  ///////////////////////////////////////
  // This is a dummy implementation
  // In a real implementation, you should get the list of topics from agnocast
  // TODO(TetsuKawa): Implement the real implementation
  ///////////////////////////////////////
  (void *)node_name;
  std::vector<std::string> topics = {
    "/chatter",
    "/another_topic_pub",
  };
  ///////////////////////////////////////

  *topic_count = topics.size();

  char ** topic_array = (char **)malloc(topics.size() * sizeof(char *));
  for (size_t i = 0; i < topics.size(); i++) {
    topic_array[i] = strdup(topics[i].c_str());
  }
  return topic_array;
}

void free_agnocast_topics(char ** topic_array, int topic_count)
{
  for (int i = 0; i < topic_count; i++) {
    free(topic_array[i]);
  }
  free(topic_array);
}
}
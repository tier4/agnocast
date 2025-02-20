
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
  std::vector<std::string> topics = {
    "/chatter",
    "/another_topic_sub",
  };
  ///////////////////////////////////////

  *topic_count = 2;

  char ** topic_array = new char *[*topic_count];  // NOLINT
  for (size_t i = 0; i < *topic_count; i++) {
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
  std::vector<std::string> topics = {
    "/chatter",
    "/another_topic_pub",
  };
  ///////////////////////////////////////

  *topic_count = 2;

  char ** topic_array = new char *[*topic_count];  // NOLINT
  for (size_t i = 0; i < *topic_count; i++) {
    topic_array[i] = strdup(topics[i].c_str());
  }
  return topic_array;
}

void free_agnocast_topics(char ** topic_array, int topic_count)
{
  for (int i = 0; i < topic_count; i++) {
    delete[] topic_array[i];  // NOLINT
  }
  delete[] topic_array;  // NOLINT
}
}
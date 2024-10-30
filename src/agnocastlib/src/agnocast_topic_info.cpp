#include "agnocast_topic_info.hpp"

namespace agnocast
{

std::mutex id2_topic_mq_info_mtx;
std::unordered_map<uint32_t, AgnocastTopicInfo> id2_topic_mq_info(
  100 /* arbitrary size to prevent rehash */);
std::atomic<uint32_t> agnocast_topic_next_id;

std::shared_ptr<std::function<void()>> create_callable(
  const void * ptr, const uint32_t publisher_pid, const uint64_t timestamp,
  const uint32_t topic_local_id)
{
  bool found;
  AgnocastTopicInfo * info;

  {
    std::lock_guard<std::mutex> lock(id2_topic_mq_info_mtx);
    auto it = id2_topic_mq_info.find(topic_local_id);
    found = it != id2_topic_mq_info.end();
    if (found) info = &it->second;
  }

  if (!found) {
    RCLCPP_ERROR(logger, "callback is not registered with topic_local_id=%d", topic_local_id);
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return std::make_shared<std::function<void()>>([ptr, publisher_pid, timestamp, info]() {
    auto typed_msg = info->message_creator(ptr, info->topic_name, publisher_pid, timestamp, true);
    info->callback(*typed_msg);
  });
}

}  // namespace agnocast

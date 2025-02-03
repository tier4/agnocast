#include "agnocast_topic_info.hpp"

namespace agnocast
{

std::mutex id2_topic_info_mtx;
const int topic_map_bkt_cnt = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, AgnocastTopicInfo> id2_topic_info(topic_map_bkt_cnt);
std::atomic<uint32_t> next_agnocast_topic_info_id;
std::atomic<bool> need_epoll_updates{false};

std::shared_ptr<std::function<void()>> create_callable(
  const void * ptr, const topic_local_id_t publisher_id, const topic_local_id_t subscriber_id,
  const uint64_t timestamp, const uint32_t agnocast_topic_info_id)
{
  bool found = false;
  AgnocastTopicInfo * info = nullptr;

  {
    std::lock_guard<std::mutex> lock(id2_topic_info_mtx);
    auto it = id2_topic_info.find(agnocast_topic_info_id);
    found = it != id2_topic_info.end();
    if (found) {
      info = &it->second;
    }
  }

  if (!found) {
    RCLCPP_ERROR(
      logger, "callback is not registered with agnocast_topic_info_id=%d", agnocast_topic_info_id);
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return std::make_shared<std::function<void()>>(
    [ptr, publisher_id, subscriber_id, timestamp, info]() {
      auto typed_msg =
        info->message_creator(ptr, info->topic_name, publisher_id, subscriber_id, timestamp);
      info->callback(*typed_msg);
    });
}

}  // namespace agnocast

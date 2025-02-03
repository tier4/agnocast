#include "agnocast_callback_info.hpp"

namespace agnocast
{

std::mutex id2_callback_info_mtx;
const int callback_map_bkt_cnt = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, CallbackInfo> id2_callback_info(callback_map_bkt_cnt);
std::atomic<uint32_t> next_callback_info_id;
std::atomic<bool> need_epoll_updates{false};

std::shared_ptr<std::function<void()>> create_callable(
  const void * ptr, const topic_local_id_t subscriber_id, const uint64_t timestamp,
  const uint32_t callback_info_id)
{
  bool found = false;
  CallbackInfo * info = nullptr;

  {
    std::lock_guard<std::mutex> lock(id2_callback_info_mtx);
    auto it = id2_callback_info.find(callback_info_id);
    found = it != id2_callback_info.end();
    if (found) {
      info = &it->second;
    }
  }

  if (!found) {
    RCLCPP_ERROR(logger, "callback is not registered with callback_info_id=%d", callback_info_id);
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return std::make_shared<std::function<void()>>([ptr, subscriber_id, timestamp, info]() {
    auto typed_msg = info->message_creator(ptr, info->topic_name, subscriber_id, timestamp);
    info->callback(*typed_msg);
  });
}

}  // namespace agnocast

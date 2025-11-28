#include "agnocast/agnocast_timer_info.hpp"
#include "agnocast/agnocast_callback_info.hpp"

namespace agnocast
{

std::mutex id2_timer_info_mtx;
std::unordered_map<uint32_t, TimerInfo> id2_timer_info;
std::atomic<uint32_t> next_timer_id{0};

uint32_t register_timer(
  std::function<void()> callback,
  std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  auto timer = std::make_shared<AgnocastTimer>(period, std::move(callback));
  const uint32_t timer_id = next_timer_id.fetch_add(1);

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    id2_timer_info[timer_id] = TimerInfo{
      timer,
      timer->get_fd(),
      callback_group,
      true  // need_epoll_update
    };
  }

  need_epoll_updates.store(true);

  return timer_id;
}

}  // namespace agnocast

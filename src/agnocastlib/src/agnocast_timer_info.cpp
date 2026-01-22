#include "agnocast/agnocast_timer_info.hpp"

#include "agnocast/agnocast_epoll.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <sys/timerfd.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <stdexcept>

namespace agnocast
{

std::mutex id2_timer_info_mtx;
std::unordered_map<uint32_t, TimerInfo> id2_timer_info;
std::atomic<uint32_t> next_timer_id{0};

int create_timer_fd(uint32_t timer_id, std::chrono::nanoseconds period)
{
  int timer_fd = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK | TFD_CLOEXEC);
  if (timer_fd == -1) {
    throw std::runtime_error(
      "timerfd_create failed for timer_id=" + std::to_string(timer_id) + ": " +
      std::strerror(errno));
  }

  struct itimerspec spec = {};
  const auto period_count = period.count();
  spec.it_interval.tv_sec = period_count / 1000000000;
  spec.it_interval.tv_nsec = period_count % 1000000000;
  spec.it_value = spec.it_interval;

  if (timerfd_settime(timer_fd, 0, &spec, nullptr) == -1) {
    const int saved_errno = errno;
    close(timer_fd);
    throw std::runtime_error(
      "timerfd_settime failed for timer_id=" + std::to_string(timer_id) +
      ", period=" + std::to_string(period_count) + "ns: " + std::strerror(saved_errno));
  }

  return timer_fd;
}

uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  const uint32_t timer_id = next_timer_id.fetch_add(1);
  if (timer_id & TIMER_EVENT_FLAG) {
    throw std::runtime_error("Timer ID overflow: too many timers created");
  }
  const int timer_fd = create_timer_fd(timer_id, period);
  const auto now = std::chrono::steady_clock::now();

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    id2_timer_info[timer_id] = TimerInfo{
      timer_fd,     std::move(callback),
      now + period,  // next_call_time
      period,       callback_group,
      true  // need_epoll_update
    };
  }

  need_epoll_updates.store(true);

  return timer_id;
}

void handle_timer_event(TimerInfo & timer_info)
{
  // Read the number of expirations to clear the event
  uint64_t expirations = 0;
  const ssize_t ret = read(timer_info.timer_fd, &expirations, sizeof(expirations));

  if (ret == -1) {
    if (errno != EAGAIN && errno != EWOULDBLOCK) {
      RCLCPP_WARN(logger, "Failed to read timer fd: %s", strerror(errno));
      return;
    }
  }

  if (expirations > 0) {
    const auto actual_call_time = std::chrono::steady_clock::now();
    TimerCallbackInfo callback_info{timer_info.next_call_time, actual_call_time};

    timer_info.callback(callback_info);

    auto next_call_time = timer_info.next_call_time + timer_info.period;
    const auto period = timer_info.period.count();

    // in case the timer has missed at least one cycle
    if (next_call_time < actual_call_time) {
      if (period == 0) {
        // a timer with a period of zero is considered always ready
        next_call_time = actual_call_time;
      } else {
        // move the next call time forward by as many periods as necessary
        const auto now_ahead = (actual_call_time - next_call_time).count();
        // rounding up without overflow
        const auto periods_ahead = 1 + (now_ahead - 1) / period;
        next_call_time += timer_info.period * periods_ahead;
      }
    }

    timer_info.next_call_time = next_call_time;
  }
}

}  // namespace agnocast

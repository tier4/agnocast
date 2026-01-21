#include "agnocast/agnocast_timer_info.hpp"

#include "agnocast/agnocast_epoll.hpp"

#include <sys/timerfd.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <stdexcept>
#include <string>

namespace agnocast
{

std::mutex id2_timer_info_mtx;
std::unordered_map<uint32_t, TimerInfo> id2_timer_info;
std::atomic<uint32_t> next_timer_id{0};

int create_timer_fd(std::chrono::nanoseconds period)
{
  int timer_fd = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK | TFD_CLOEXEC);
  if (timer_fd == -1) {
    throw std::runtime_error(std::string("timerfd_create failed: ") + std::strerror(errno));
  }

  struct itimerspec spec = {};
  const auto period_count = period.count();
  spec.it_interval.tv_sec = period_count / 1000000000;
  spec.it_interval.tv_nsec = period_count % 1000000000;
  spec.it_value = spec.it_interval;

  if (timerfd_settime(timer_fd, 0, &spec, nullptr) == -1) {
    const int saved_errno = errno;
    close(timer_fd);
    throw std::runtime_error(std::string("timerfd_settime failed: ") + std::strerror(saved_errno));
  }

  return timer_fd;
}

uint32_t allocate_timer_id()
{
  return next_timer_id.fetch_add(1);
}

void register_timer_info(
  uint32_t timer_id, std::shared_ptr<TimerBase> timer, std::chrono::nanoseconds period,
  rclcpp::CallbackGroup::SharedPtr callback_group)
{
  const int timer_fd = create_timer_fd(period);
  const auto now = std::chrono::steady_clock::now();

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    id2_timer_info[timer_id] = TimerInfo{
      timer_fd,
      timer,         // weak_ptr to Timer
      {},            // callback (empty for WallTimer)
      now + period,  // next_call_time
      period,       std::move(callback_group),
      true,  // need_epoll_update
      false  // is_canceled
    };
  }

  need_epoll_updates.store(true);
}

uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  rclcpp::CallbackGroup::SharedPtr callback_group)
{
  const int timer_fd = create_timer_fd(period);
  const uint32_t timer_id = next_timer_id.fetch_add(1);
  const auto now = std::chrono::steady_clock::now();

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    id2_timer_info[timer_id] = TimerInfo{
      timer_fd,
      {},  // timer (empty for tf2 timers)
      std::move(callback),
      now + period,  // next_call_time
      period,
      callback_group,
      true,  // need_epoll_update
      false  // is_canceled
    };
  }

  need_epoll_updates.store(true);

  return timer_id;
}

void cancel_timer(uint32_t timer_id)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  auto it = id2_timer_info.find(timer_id);
  if (it == id2_timer_info.end()) {
    throw std::out_of_range("Timer ID not found: " + std::to_string(timer_id));
  }

  TimerInfo & info = it->second;
  if (info.is_canceled) {
    return;  // Already canceled
  }

  // Disarm the timer by setting interval to zero
  struct itimerspec spec = {};
  if (timerfd_settime(info.timer_fd, 0, &spec, nullptr) == -1) {
    throw std::runtime_error(
      std::string("timerfd_settime failed in cancel: ") + std::strerror(errno));
  }

  info.is_canceled = true;
}

void reset_timer(uint32_t timer_id)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  auto it = id2_timer_info.find(timer_id);
  if (it == id2_timer_info.end()) {
    throw std::out_of_range("Timer ID not found: " + std::to_string(timer_id));
  }

  TimerInfo & info = it->second;

  // Re-arm the timer with the original period
  struct itimerspec spec = {};
  const auto period_count = info.period.count();
  spec.it_interval.tv_sec = period_count / 1000000000;
  spec.it_interval.tv_nsec = period_count % 1000000000;
  spec.it_value = spec.it_interval;

  if (timerfd_settime(info.timer_fd, 0, &spec, nullptr) == -1) {
    throw std::runtime_error(
      std::string("timerfd_settime failed in reset: ") + std::strerror(errno));
  }

  info.is_canceled = false;
  info.next_call_time = std::chrono::steady_clock::now() + info.period;
}

void remove_timer(uint32_t timer_id)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  auto it = id2_timer_info.find(timer_id);
  if (it == id2_timer_info.end()) {
    throw std::out_of_range("Timer ID not found: " + std::to_string(timer_id));
  }

  // Close the timer fd
  close(it->second.timer_fd);

  // Remove from map
  id2_timer_info.erase(it);

  // Signal that epoll needs to be updated (to remove the fd)
  need_epoll_updates.store(true);
}

void handle_timer_event(TimerInfo & timer_info)
{
  // Read the number of expirations to clear the event
  uint64_t expirations = 0;
  const ssize_t ret = read(timer_info.timer_fd, &expirations, sizeof(expirations));

  if (ret == -1) {
    if (errno != EAGAIN && errno != EWOULDBLOCK) {
      return;
    }
  }

  if (expirations > 0) {
    const auto actual_call_time = std::chrono::steady_clock::now();
    TimerCallbackInfo callback_info{timer_info.next_call_time, actual_call_time};

    // Check if this is a WallTimer (has timer weak_ptr) or a tf2 timer (has callback)
    auto timer = timer_info.timer.lock();
    if (timer) {
      // WallTimer case
      timer->execute_callback(callback_info);
    } else if (timer_info.callback) {
      // tf2 timer case
      timer_info.callback(callback_info);
    } else {
      return;  // Timer object has been destroyed and no callback
    }

    auto next_call_time = timer_info.next_call_time + timer_info.period;
    const auto period = timer_info.period.count();

    // in case the timer has missed at least once cycle
    if (next_call_time < actual_call_time) {
      // move the next call time forward by as many periods as necessary
      const auto now_ahead = (actual_call_time - next_call_time).count();
      // rounding up without overflow
      const auto periods_ahead = 1 + (now_ahead - 1) / period;
      next_call_time += timer_info.period * periods_ahead;
    }

    timer_info.next_call_time = next_call_time;
  }
}

}  // namespace agnocast

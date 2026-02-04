#include "agnocast/agnocast_timer.hpp"

#include "agnocast/agnocast_timer_info.hpp"

#include <sys/timerfd.h>
#include <unistd.h>

namespace agnocast
{

TimerBase::~TimerBase()
{
  unregister_timer_info(timer_id_);
}

void TimerBase::cancel()
{
  canceled_.store(true, std::memory_order_release);

  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  const auto it = id2_timer_info.find(timer_id_);
  if (it == id2_timer_info.end()) {
    return;
  }
  auto & info = *it->second;

  // Disarm timerfd to stop epoll wakeups
  if (info.timer_fd >= 0) {
    struct itimerspec spec = {};
    timerfd_settime(info.timer_fd, 0, &spec, nullptr);
  }
}

bool TimerBase::is_canceled() const
{
  return canceled_.load(std::memory_order_acquire);
}

void TimerBase::reset()
{
  canceled_.store(false, std::memory_order_release);

  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  const auto it = id2_timer_info.find(timer_id_);
  if (it == id2_timer_info.end()) {
    return;
  }
  auto & info = *it->second;

  const int64_t now_ns = info.clock->now().nanoseconds();
  const int64_t period_ns = info.period.count();
  info.next_call_time_ns.store(now_ns + period_ns, std::memory_order_relaxed);
  info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);

  // Re-arm timerfd
  if (info.timer_fd >= 0) {
    struct itimerspec spec = {};
    if (period_ns == 0) {
      spec.it_interval.tv_nsec = 1;
    } else {
      spec.it_interval.tv_sec = period_ns / NANOSECONDS_PER_SECOND;
      spec.it_interval.tv_nsec = period_ns % NANOSECONDS_PER_SECOND;
    }
    spec.it_value = spec.it_interval;
    timerfd_settime(info.timer_fd, 0, &spec, nullptr);
  }

  // For ROS_TIME timers without timerfd (sim time active), wake epoll via clock_eventfd
  if (info.timer_fd < 0 && info.clock_eventfd >= 0) {
    const uint64_t val = 1;
    [[maybe_unused]] auto _ = write(info.clock_eventfd, &val, sizeof(val));
  }
}

std::chrono::nanoseconds TimerBase::time_until_trigger() const
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  const auto it = id2_timer_info.find(timer_id_);
  if (it == id2_timer_info.end()) {
    return std::chrono::nanoseconds::max();
  }
  const auto & info = *it->second;

  const int64_t now_ns = info.clock->now().nanoseconds();
  const int64_t next_ns = info.next_call_time_ns.load(std::memory_order_relaxed);
  const int64_t remaining = next_ns - now_ns;
  return std::chrono::nanoseconds(remaining > 0 ? remaining : 0);
}

std::chrono::nanoseconds TimerBase::exchange_period(std::chrono::nanoseconds new_period)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  const auto it = id2_timer_info.find(timer_id_);
  if (it == id2_timer_info.end()) {
    return period_;
  }
  auto & info = *it->second;

  const std::chrono::nanoseconds old_period = info.period;
  info.period = new_period;
  period_ = new_period;

  // Update next call time based on new period
  const int64_t last_call_ns = info.last_call_time_ns.load(std::memory_order_relaxed);
  info.next_call_time_ns.store(last_call_ns + new_period.count(), std::memory_order_relaxed);

  // Re-arm timerfd with new period
  if (info.timer_fd >= 0) {
    const auto period_count = new_period.count();
    struct itimerspec spec = {};
    if (period_count == 0) {
      spec.it_interval.tv_nsec = 1;
    } else {
      spec.it_interval.tv_sec = period_count / NANOSECONDS_PER_SECOND;
      spec.it_interval.tv_nsec = period_count % NANOSECONDS_PER_SECOND;
    }
    spec.it_value = spec.it_interval;
    timerfd_settime(info.timer_fd, 0, &spec, nullptr);
  }

  return old_period;
}

}  // namespace agnocast

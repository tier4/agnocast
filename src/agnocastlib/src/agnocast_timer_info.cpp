#include "agnocast/agnocast_timer_info.hpp"

#include "agnocast/agnocast_epoll.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <sys/eventfd.h>
#include <sys/timerfd.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <stdexcept>
#include <string>

namespace agnocast
{

std::mutex id2_timer_info_mtx;
std::unordered_map<uint32_t, std::shared_ptr<TimerInfo>> id2_timer_info;
std::atomic<uint32_t> next_timer_id{0};

namespace
{

int64_t get_current_time_ns(const rclcpp::Clock::SharedPtr & clock)
{
  if (clock) {
    return clock->now().nanoseconds();
  }
  return to_nanoseconds(std::chrono::steady_clock::now());
}

}  // namespace

void handle_pre_time_jump(TimerInfo & timer_info)
{
  const int64_t now_ns = timer_info.clock->now().nanoseconds();
  if (now_ns == 0) {
    // No time credit if clock is uninitialized
    return;
  }
  // Source of time may be changing, save elapsed duration pre jump
  // so the timer only waits the remainder in the new epoch (if clock_change occurs)
  const int64_t next_call_ns = timer_info.next_call_time_ns.load(std::memory_order_relaxed);
  timer_info.time_credit.store(next_call_ns - now_ns, std::memory_order_relaxed);
}

void handle_post_time_jump(TimerInfo & timer_info, const rcl_time_jump_t & jump)
{
  const int64_t now_ns = timer_info.clock->now().nanoseconds();
  const int64_t last_call_ns = timer_info.last_call_time_ns.load(std::memory_order_relaxed);
  const int64_t next_call_ns = timer_info.next_call_time_ns.load(std::memory_order_relaxed);
  const int64_t period_ns = timer_info.period.count();

  if (jump.clock_change == RCL_ROS_TIME_ACTIVATED) {
    // ROS time activated: close timerfd (simulation time will use clock_eventfd)
    if (timer_info.timer_fd >= 0) {
      close(timer_info.timer_fd);
      timer_info.timer_fd = -1;
    }

    if (now_ns == 0) {
      return;
    }
    const int64_t time_credit = timer_info.time_credit.exchange(0, std::memory_order_relaxed);
    if (time_credit != 0) {
      timer_info.next_call_time_ns.store(
        now_ns - time_credit + period_ns, std::memory_order_relaxed);
      timer_info.last_call_time_ns.store(now_ns - time_credit, std::memory_order_relaxed);
    }
  } else if (jump.clock_change == RCL_ROS_TIME_DEACTIVATED) {
    // ROS time deactivated: recreate timerfd (back to system time)
    if (timer_info.timer_fd < 0) {
      timer_info.timer_fd = create_timer_fd(timer_info.period);
      timer_info.need_epoll_update = true;
      need_epoll_updates.store(true);
    }

    if (now_ns == 0) {
      return;
    }
    const int64_t time_credit = timer_info.time_credit.exchange(0, std::memory_order_relaxed);
    if (time_credit != 0) {
      timer_info.next_call_time_ns.store(
        now_ns - time_credit + period_ns, std::memory_order_relaxed);
      timer_info.last_call_time_ns.store(now_ns - time_credit, std::memory_order_relaxed);
    }
  } else if (next_call_ns <= now_ns) {
    // Post forward jump and timer is ready - wake up epoll
    timer_info.time_credit.store(0, std::memory_order_relaxed);  // Clear unused time_credit
    if (timer_info.clock_eventfd >= 0) {
      const uint64_t val = 1;
      [[maybe_unused]] auto _ = write(timer_info.clock_eventfd, &val, sizeof(val));
    }
  } else if (now_ns < last_call_ns) {
    // Post backwards time jump that went further back than 1 period
    // Next callback should happen after 1 period
    timer_info.time_credit.store(0, std::memory_order_relaxed);  // Clear unused time_credit
    timer_info.next_call_time_ns.store(now_ns + period_ns, std::memory_order_relaxed);
    timer_info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);
  } else {
    // Other cases (small forward jump where timer is not ready)
    timer_info.time_credit.store(0, std::memory_order_relaxed);  // Clear unused time_credit
  }
}

void setup_time_jump_callback(TimerInfo & timer_info, const rclcpp::Clock::SharedPtr & clock)
{
  if (!clock || clock->get_clock_type() != RCL_ROS_TIME) {
    return;
  }

  rcl_jump_threshold_t threshold;
  threshold.on_clock_change = true;
  threshold.min_forward.nanoseconds = 1;
  threshold.min_backward.nanoseconds = -1;

  timer_info.jump_handler = clock->create_jump_callback(
    [&timer_info]() { handle_pre_time_jump(timer_info); },
    [&timer_info](const rcl_time_jump_t & jump) { handle_post_time_jump(timer_info, jump); },
    threshold);
}

TimerInfo::~TimerInfo()
{
  if (timer_fd >= 0) {
    close(timer_fd);
  }
  if (clock_eventfd >= 0) {
    close(clock_eventfd);
  }
}

int create_timer_fd(std::chrono::nanoseconds period)
{
  int timer_fd = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK | TFD_CLOEXEC);
  if (timer_fd == -1) {
    throw std::runtime_error(std::string("timerfd_create failed: ") + std::strerror(errno));
  }

  struct itimerspec spec = {};
  const auto period_count = period.count();
  if (period_count == 0) {
    // Workaround: timerfd_settime() disarms the timer when both it_value and it_interval
    // are zero. Use 1ns to keep the timer armed and achieve "always ready" semantics.
    spec.it_interval.tv_sec = 0;
    spec.it_interval.tv_nsec = 1;
  } else {
    spec.it_interval.tv_sec = period_count / NANOSECONDS_PER_SECOND;
    spec.it_interval.tv_nsec = period_count % NANOSECONDS_PER_SECOND;
  }
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
  const uint32_t timer_id = next_timer_id.fetch_add(1);
  if ((timer_id & TIMER_EVENT_FLAG) != 0U) {
    throw std::runtime_error("Timer ID overflow: too many timers created");
  }
  return timer_id;
}

void register_timer_info(
  uint32_t timer_id, std::shared_ptr<TimerBase> timer, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr & callback_group, rclcpp::Clock::SharedPtr clock)
{
  const bool is_ros_time = clock && (clock->get_clock_type() == RCL_ROS_TIME);
  const int64_t now_ns = get_current_time_ns(clock);

  auto timer_info = std::make_shared<TimerInfo>();
  timer_info->timer_id = timer_id;
  timer_info->timer = timer;
  timer_info->last_call_time_ns.store(now_ns, std::memory_order_relaxed);
  timer_info->next_call_time_ns.store(now_ns + period.count(), std::memory_order_relaxed);
  timer_info->period = period;
  timer_info->callback_group = callback_group;
  timer_info->need_epoll_update = true;
  timer_info->is_canceled = false;
  timer_info->clock = clock;

  // All timers use timerfd for wall clock based firing
  timer_info->timer_fd = create_timer_fd(period);

  if (is_ros_time) {
    // ROS_TIME timers also use clock_eventfd for simulation time support
    timer_info->clock_eventfd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
    if (timer_info->clock_eventfd == -1) {
      close(timer_info->timer_fd);
      throw std::runtime_error(
        "eventfd creation failed for timer_id=" + std::to_string(timer_id) + ": " +
        std::strerror(errno));
    }
  }

  setup_time_jump_callback(*timer_info, clock);

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    id2_timer_info[timer_id] = std::move(timer_info);
  }

  need_epoll_updates.store(true);
}

uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  rclcpp::CallbackGroup::SharedPtr callback_group)
{
  const int timer_fd = create_timer_fd(period);
  const uint32_t timer_id = next_timer_id.fetch_add(1);
  const int64_t now_ns = to_nanoseconds(std::chrono::steady_clock::now());

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    auto timer_info = std::make_shared<TimerInfo>();
    timer_info->timer_id = timer_id;
    timer_info->timer_fd = timer_fd;
    // timer is empty for tf2 timers
    timer_info->callback = std::move(callback);
    timer_info->callback_group = callback_group;
    timer_info->last_call_time_ns.store(now_ns, std::memory_order_relaxed);
    timer_info->next_call_time_ns.store(now_ns + period.count(), std::memory_order_relaxed);
    timer_info->period = period;
    timer_info->need_epoll_update = true;
    timer_info->is_canceled = false;
    // clock is nullptr for tf2 timers (uses steady_clock)

    id2_timer_info[timer_id] = std::move(timer_info);
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

  TimerInfo & info = *it->second;
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

  TimerInfo & info = *it->second;

  // Re-arm the timer with the original period
  struct itimerspec spec = {};
  const auto period_count = info.period.count();
  spec.it_interval.tv_sec = period_count / NANOSECONDS_PER_SECOND;
  spec.it_interval.tv_nsec = period_count % NANOSECONDS_PER_SECOND;
  spec.it_value = spec.it_interval;

  if (timerfd_settime(info.timer_fd, 0, &spec, nullptr) == -1) {
    throw std::runtime_error(
      std::string("timerfd_settime failed in reset: ") + std::strerror(errno));
  }

  info.is_canceled = false;
  const int64_t now_ns = get_current_time_ns(info.clock);
  info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);
  info.next_call_time_ns.store(now_ns + period_count, std::memory_order_relaxed);
}

void remove_timer(uint32_t timer_id)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  auto it = id2_timer_info.find(timer_id);
  if (it == id2_timer_info.end()) {
    throw std::out_of_range("Timer ID not found: " + std::to_string(timer_id));
  }

  // Remove from map (TimerInfo destructor will close timer_fd)
  id2_timer_info.erase(it);

  // Signal that epoll needs to be updated (to remove the fd)
  need_epoll_updates.store(true);
}

void handle_timer_event(TimerInfo & timer_info)
{
  if (timer_info.is_canceled) {
    return;
  }

  // Read the number of expirations to clear the timerfd event
  uint64_t expirations = 0;
  const ssize_t ret = read(timer_info.timer_fd, &expirations, sizeof(expirations));

  if (ret == -1) {
    if (errno != EAGAIN && errno != EWOULDBLOCK) {
      RCLCPP_WARN(logger, "Failed to read timer fd: %s", strerror(errno));
      return;
    }
  }

  if (expirations > 0) {
    // Use clock-based time if available, otherwise use steady_clock
    const int64_t now_ns = get_current_time_ns(timer_info.clock);
    const int64_t expected_call_time_ns =
      timer_info.next_call_time_ns.load(std::memory_order_relaxed);

    timer_info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);

    // Check if this is a WallTimer (has timer weak_ptr) or a tf2 timer (has callback)
    auto timer = timer_info.timer.lock();
    if (timer) {
      // WallTimer case
      timer->execute_callback();
    } else if (timer_info.callback) {
      // tf2 timer case - create TimerCallbackInfo for the callback
      const auto expected_time =
        std::chrono::steady_clock::time_point(std::chrono::nanoseconds(expected_call_time_ns));
      const auto actual_time =
        std::chrono::steady_clock::time_point(std::chrono::nanoseconds(now_ns));
      TimerCallbackInfo callback_info{expected_time, actual_time};
      timer_info.callback(callback_info);
    } else {
      return;  // Timer object has been destroyed and no callback
    }

    const int64_t period_ns = timer_info.period.count();
    int64_t next_call_time_ns = expected_call_time_ns + period_ns;

    // in case the timer has missed at least one cycle
    if (next_call_time_ns < now_ns) {
      if (period_ns == 0) {
        // a timer with a period of zero is considered always ready
        next_call_time_ns = now_ns;
      } else {
        // move the next call time forward by as many periods as necessary
        const int64_t now_ahead = now_ns - next_call_time_ns;
        // rounding up without overflow
        const int64_t periods_ahead = 1 + (now_ahead - 1) / period_ns;
        next_call_time_ns += periods_ahead * period_ns;
      }
    }
    timer_info.next_call_time_ns.store(next_call_time_ns, std::memory_order_relaxed);
  }
}

void handle_clock_event(TimerInfo & timer_info)
{
  if (timer_info.is_canceled) {
    return;
  }

  // Read eventfd to clear the event
  uint64_t val = 0;
  const ssize_t ret = read(timer_info.clock_eventfd, &val, sizeof(val));

  if (ret == -1) {
    if (errno != EAGAIN && errno != EWOULDBLOCK) {
      RCLCPP_WARN(logger, "Failed to read clock eventfd: %s", strerror(errno));
      return;
    }
  }

  if (val > 0) {
    // Use clock-based time
    const int64_t now_ns = timer_info.clock->now().nanoseconds();
    const int64_t next_call_ns = timer_info.next_call_time_ns.load(std::memory_order_relaxed);

    // Check if timer is ready (for simulation time support)
    if (now_ns < next_call_ns) {
      return;  // Not ready yet
    }

    auto timer = timer_info.timer.lock();
    if (!timer) {
      return;  // Timer object has been destroyed
    }

    timer_info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);

    const int64_t period_ns = timer_info.period.count();
    int64_t new_next_call_ns = next_call_ns + period_ns;

    // In case the timer has missed at least one cycle
    if (new_next_call_ns < now_ns) {
      if (period_ns == 0) {
        new_next_call_ns = now_ns;
      } else {
        const int64_t now_ahead = now_ns - new_next_call_ns;
        const int64_t periods_ahead = 1 + (now_ahead - 1) / period_ns;
        new_next_call_ns += periods_ahead * period_ns;
      }
    }
    timer_info.next_call_time_ns.store(new_next_call_ns, std::memory_order_relaxed);

    timer->execute_callback();
  }
}

void unregister_timer_info(uint32_t timer_id)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  id2_timer_info.erase(timer_id);
}

}  // namespace agnocast

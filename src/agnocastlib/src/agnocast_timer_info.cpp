#include "agnocast/agnocast_timer_info.hpp"

#include "agnocast/agnocast_epoll.hpp"
#include "agnocast/agnocast_utils.hpp"

#include <sys/eventfd.h>
#include <sys/timerfd.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <stdexcept>

namespace agnocast
{

std::mutex id2_timer_info_mtx;
std::unordered_map<uint32_t, std::shared_ptr<TimerInfo>> id2_timer_info;
std::atomic<uint32_t> next_timer_id{0};

void handle_pre_time_jump(TimerInfo & timer_info)
{
  // Save current time before the jump
  const int64_t now_ns = timer_info.clock->now().nanoseconds();
  timer_info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);
}

void handle_post_time_jump(TimerInfo & timer_info, const rcl_time_jump_t & jump)
{
  const int64_t now_ns = timer_info.clock->now().nanoseconds();
  const int64_t period_ns = timer_info.period.count();

  if (
    jump.clock_change == RCL_ROS_TIME_ACTIVATED || jump.clock_change == RCL_ROS_TIME_DEACTIVATED) {
    // ROS time activated or deactivated: reset timer based on saved last_call_time
    if (now_ns == 0) {
      timer_info.next_call_time_ns.store(period_ns, std::memory_order_relaxed);
    } else {
      const int64_t last_ns = timer_info.last_call_time_ns.load(std::memory_order_relaxed);
      timer_info.next_call_time_ns.store(last_ns + period_ns, std::memory_order_relaxed);
    }
  } else if (jump.delta.nanoseconds < 0) {
    // Backward jump: reset timer to fire after one period from now
    timer_info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);
    timer_info.next_call_time_ns.store(now_ns + period_ns, std::memory_order_relaxed);
  } else {
    // Forward jump: adjust next fire time if we're behind
    const int64_t next_ns = timer_info.next_call_time_ns.load(std::memory_order_relaxed);
    if (next_ns < now_ns && period_ns > 0) {
      const int64_t periods_missed = (now_ns - next_ns) / period_ns + 1;
      timer_info.next_call_time_ns.store(
        next_ns + periods_missed * period_ns, std::memory_order_relaxed);
    }
  }

  // Wake up epoll to check if timer should fire
  if (timer_info.clock_eventfd >= 0) {
    const uint64_t val = 1;
    // Ignore write errors (e.g., if eventfd counter overflows)
    [[maybe_unused]] auto _ = write(timer_info.clock_eventfd, &val, sizeof(val));
  }
}

void setup_time_jump_callback(TimerInfo & timer_info, const rclcpp::Clock::SharedPtr & clock)
{
  if (clock->get_clock_type() != RCL_ROS_TIME) {
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
    throw std::runtime_error(
      "timerfd_settime failed for timer_id=" + std::to_string(timer_id) +
      ", period=" + std::to_string(period_count) + "ns: " + std::strerror(saved_errno));
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
  const int timer_fd = create_timer_fd(timer_id, period);
  const int64_t now_ns = clock->now().nanoseconds();

  auto timer_info = std::make_shared<TimerInfo>();
  timer_info->timer_fd = timer_fd;
  timer_info->timer = timer;
  timer_info->last_call_time_ns.store(now_ns, std::memory_order_relaxed);
  timer_info->next_call_time_ns.store(now_ns + period.count(), std::memory_order_relaxed);
  timer_info->period = period;
  timer_info->callback_group = callback_group;
  timer_info->need_epoll_update = true;
  timer_info->clock = clock;

  // Create eventfd for ROS_TIME timers to wake epoll on clock updates
  if (clock->get_clock_type() == RCL_ROS_TIME) {
    timer_info->clock_eventfd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
    if (timer_info->clock_eventfd == -1) {
      close(timer_fd);
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

// Check if timer is ready and execute callback if so
// Returns true if callback was executed
bool check_and_execute_timer(TimerInfo & timer_info)
{
  auto timer = timer_info.timer.lock();
  if (!timer) {
    return false;  // Timer object has been destroyed
  }

  const int64_t now_ns = timer_info.clock->now().nanoseconds();
  const int64_t next_call_ns = timer_info.next_call_time_ns.load(std::memory_order_relaxed);
  const int64_t period_ns = timer_info.period.count();

  // Check if timer is ready (for simulation time support)
  if (now_ns < next_call_ns) {
    return false;  // Not ready yet
  }

  // Update timing
  timer_info.last_call_time_ns.store(now_ns, std::memory_order_relaxed);

  int64_t new_next_call_ns = next_call_ns + period_ns;

  // In case the timer has missed at least one cycle
  if (new_next_call_ns < now_ns) {
    if (period_ns == 0) {
      // A timer with a period of zero is considered always ready
      new_next_call_ns = now_ns;
    } else {
      // Move the next call time forward by as many periods as necessary
      const int64_t now_ahead = now_ns - new_next_call_ns;
      // Rounding up without overflow
      const int64_t periods_ahead = 1 + (now_ahead - 1) / period_ns;
      new_next_call_ns += periods_ahead * period_ns;
    }
  }
  timer_info.next_call_time_ns.store(new_next_call_ns, std::memory_order_relaxed);

  timer->execute_callback();
  return true;
}

void handle_timer_event(TimerInfo & timer_info)
{
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
    check_and_execute_timer(timer_info);
  }
}

void handle_clock_event(TimerInfo & timer_info)
{
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
    check_and_execute_timer(timer_info);
  }
}

void unregister_timer_info(uint32_t timer_id)
{
  std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
  id2_timer_info.erase(timer_id);
}

}  // namespace agnocast

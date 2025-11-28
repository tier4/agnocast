#include "agnocast/agnocast_timer.hpp"

#include <sys/timerfd.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>

namespace agnocast
{

AgnocastTimer::AgnocastTimer(std::chrono::nanoseconds period, std::function<void()> callback)
: timer_fd_(-1), callback_(std::move(callback)), canceled_(false)
{
  // Create timer file descriptor
  timer_fd_ = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK | TFD_CLOEXEC);
  if (timer_fd_ == -1) {
    throw std::runtime_error(std::string("timerfd_create failed: ") + std::strerror(errno));
  }

  // Configure timer period
  struct itimerspec spec = {};
  const auto period_count = period.count();
  spec.it_interval.tv_sec = period_count / 1000000000;
  spec.it_interval.tv_nsec = period_count % 1000000000;
  spec.it_value = spec.it_interval;  // Initial expiration same as interval

  if (timerfd_settime(timer_fd_, 0, &spec, nullptr) == -1) {
    const int saved_errno = errno;
    close(timer_fd_);
    timer_fd_ = -1;
    throw std::runtime_error(std::string("timerfd_settime failed: ") + std::strerror(saved_errno));
  }
}

AgnocastTimer::~AgnocastTimer()
{
  if (timer_fd_ >= 0) {
    close(timer_fd_);
    timer_fd_ = -1;
  }
}

int AgnocastTimer::get_fd() const
{
  return timer_fd_;
}

void AgnocastTimer::handle_event()
{
  if (canceled_.load()) {
    return;
  }

  // Read the number of expirations
  uint64_t expirations = 0;
  const ssize_t ret = read(timer_fd_, &expirations, sizeof(expirations));

  if (ret == -1) {
    if (errno != EAGAIN && errno != EWOULDBLOCK) {
      // Log error but don't throw - we're in event handling context
      return;
    }
  }

  // Execute the callback
  if (callback_ && expirations > 0) {
    callback_();
  }
}

void AgnocastTimer::cancel()
{
  if (canceled_.exchange(true)) {
    return;  // Already canceled
  }

  // Disarm the timer by setting both intervals to zero
  struct itimerspec spec = {};
  spec.it_interval.tv_sec = 0;
  spec.it_interval.tv_nsec = 0;
  spec.it_value.tv_sec = 0;
  spec.it_value.tv_nsec = 0;

  timerfd_settime(timer_fd_, 0, &spec, nullptr);
}

bool AgnocastTimer::is_canceled() const
{
  return canceled_.load();
}

void AgnocastTimer::reset(std::chrono::nanoseconds period)
{
  canceled_.store(false);

  struct itimerspec spec = {};
  const auto period_count = period.count();
  spec.it_interval.tv_sec = period_count / 1000000000;
  spec.it_interval.tv_nsec = period_count % 1000000000;
  spec.it_value = spec.it_interval;

  if (timerfd_settime(timer_fd_, 0, &spec, nullptr) == -1) {
    throw std::runtime_error(std::string("timerfd_settime failed: ") + std::strerror(errno));
  }
}

}  // namespace agnocast

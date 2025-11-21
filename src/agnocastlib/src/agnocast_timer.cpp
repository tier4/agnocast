// Copyright 2025 Agnocast
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
    throw std::runtime_error(
            std::string("timerfd_create failed: ") + std::strerror(errno));
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
    throw std::runtime_error(
            std::string("timerfd_settime failed: ") + std::strerror(saved_errno));
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
  if (canceled_) {
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
  if (canceled_) {
    return;
  }

  canceled_ = true;

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
  return canceled_;
}

void AgnocastTimer::reset(std::chrono::nanoseconds period)
{
  canceled_ = false;

  struct itimerspec spec = {};
  const auto period_count = period.count();
  spec.it_interval.tv_sec = period_count / 1000000000;
  spec.it_interval.tv_nsec = period_count % 1000000000;
  spec.it_value = spec.it_interval;

  if (timerfd_settime(timer_fd_, 0, &spec, nullptr) == -1) {
    throw std::runtime_error(
            std::string("timerfd_settime failed: ") + std::strerror(errno));
  }
}

}  // namespace agnocast

#pragma once

#include "agnocast/agnocast_event_source.hpp"
#include "agnocast/agnocast_subscription_info.hpp"
#include "agnocast/agnocast_timer_info.hpp"
#include "sys/epoll.h"

#include <mutex>
#include <vector>

namespace agnocast
{

// Event type flags for epoll event identification
// Using high bits to distinguish event sources
constexpr uint32_t SUBSCRIPTION_EVENT_FLAG = 0x00000000;
constexpr uint32_t TIMER_EVENT_FLAG = 0x80000000;

/// Wait for epoll event and dispatch to appropriate handler.
/// @param epoll_fd The epoll file descriptor
/// @param my_pid Current process ID (for CARET tracing)
/// @param timeout_ms Timeout in milliseconds for epoll_wait
/// @param ready_agnocast_executables_mutex Mutex for ready executables vector
/// @param ready_agnocast_executables Vector to store ready executables
void wait_and_handle_epoll_event(
  int epoll_fd, pid_t my_pid, int timeout_ms,
  std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables);

/// Prepare epoll by registering all event sources that need update.
/// @tparam ValidateFn Validator function type for callback group
/// @param epoll_fd The epoll file descriptor
/// @param my_pid Current process ID (for CARET tracing)
/// @param ready_agnocast_executables_mutex Mutex for ready executables vector
/// @param ready_agnocast_executables Vector to store ready executables
/// @param validate_callback_group Function to validate callback group ownership
template <class ValidateFn>
void prepare_epoll_impl(
  int epoll_fd, pid_t my_pid, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables,
  ValidateFn && validate_callback_group);

}  // namespace agnocast

// Template implementation
namespace agnocast
{

template <class ValidateFn>
void prepare_epoll_impl(
  const int epoll_fd, const pid_t my_pid, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables,
  ValidateFn && validate_callback_group)
{
  // Register subscription callbacks to epoll
  {
    std::lock_guard<std::mutex> lock(id2_subscription_info_mtx);

    for (auto & it : id2_subscription_info) {
      const uint32_t subscription_id = it.first;
      SubscriptionInfo & subscription_info = it.second;

      if (!subscription_info.need_epoll_update) {
        continue;
      }

      if (!validate_callback_group(subscription_info.callback_group)) {
        continue;
      }

      struct epoll_event ev = {};
      ev.events = EPOLLIN;
      ev.data.u32 = subscription_id | SUBSCRIPTION_EVENT_FLAG;

      if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, subscription_info.mqdes, &ev) == -1) {
        RCLCPP_ERROR(logger, "epoll_ctl failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      if (subscription_info.is_transient_local) {
        agnocast::receive_message(
          subscription_id, my_pid, subscription_info, ready_agnocast_executables_mutex,
          ready_agnocast_executables);
      }

      subscription_info.need_epoll_update = false;
    }
  }

  // Register timers to epoll
  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);

    for (auto & it : id2_timer_info) {
      const uint32_t timer_id = it.first;
      TimerInfo & timer_info = it.second;

      if (!timer_info.need_epoll_update) {
        continue;
      }

      if (!validate_callback_group(timer_info.callback_group)) {
        continue;
      }

      struct epoll_event ev = {};
      ev.events = EPOLLIN;
      ev.data.u32 = timer_id | TIMER_EVENT_FLAG;

      if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, timer_info.timer_fd, &ev) == -1) {
        RCLCPP_ERROR(logger, "epoll_ctl failed for timer: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      timer_info.need_epoll_update = false;
    }
  }

  // Check if all updates are done
  const bool all_subscriptions_updated = [&]() {
    std::lock_guard<std::mutex> lock(id2_subscription_info_mtx);
    return std::none_of(
      id2_subscription_info.begin(), id2_subscription_info.end(),
      [](const auto & it) { return it.second.need_epoll_update; });
  }();

  const bool all_timers_updated = [&]() {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    return std::none_of(id2_timer_info.begin(), id2_timer_info.end(), [](const auto & it) {
      return it.second.need_epoll_update;
    });
  }();

  if (all_subscriptions_updated && all_timers_updated) {
    need_epoll_updates.store(false);
  }
}

}  // namespace agnocast

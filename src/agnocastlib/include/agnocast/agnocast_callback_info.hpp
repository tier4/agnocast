#pragma once

#include "agnocast/agnocast_smart_pointer.hpp"
#include "sys/epoll.h"

#include <chrono>
#include <mutex>
#include <type_traits>

namespace agnocast
{

class AgnocastExecutable;

// Base class for a type-erased object
class AnyObject
{
public:
  virtual ~AnyObject() = default;
  virtual const std::type_info & type() const = 0;
};

// Class for a specific message type
template <typename T>
class TypedMessagePtr : public AnyObject
{
  agnocast::ipc_shared_ptr<T> ptr_;

public:
  explicit TypedMessagePtr(agnocast::ipc_shared_ptr<T> p) : ptr_(std::move(p)) {}

  const std::type_info & type() const override { return typeid(T); }

  agnocast::ipc_shared_ptr<T> && get() && { return std::move(ptr_); }
};

// Type for type-erased callback function
using TypeErasedCallback = std::function<void(AnyObject &&)>;

// Timer callback info passed to timer callbacks
struct TimerCallbackInfo
{
  std::chrono::steady_clock::time_point expected_call_time;
  std::chrono::steady_clock::time_point actual_call_time;
};

// Unified executable info for both subscriptions and timers
struct ExecutableInfo
{
  enum class Type { Subscription, Timer };

  Type type;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  bool need_epoll_update = true;
  int fd;  // mqdes for subscription, timer_fd for timer

  // Subscription specific (only valid when type == Subscription)
  std::string topic_name;
  topic_local_id_t subscriber_id;
  bool is_transient_local;
  TypeErasedCallback subscription_callback;
  std::function<std::unique_ptr<AnyObject>(
    const void *, const std::string &, const topic_local_id_t, const uint64_t)>
    message_creator;

  // Timer specific (only valid when type == Timer)
  std::function<void(TimerCallbackInfo &)> timer_callback;
  std::chrono::steady_clock::time_point next_call_time;
  std::chrono::nanoseconds period;
};

std::vector<std::string> get_agnocast_topics_by_group(
  const rclcpp::CallbackGroup::SharedPtr & group);

extern std::mutex id2_executable_info_mtx;
extern std::unordered_map<uint32_t, ExecutableInfo> id2_executable_info;
extern std::atomic<uint32_t> next_executable_id;
extern std::atomic<bool> need_epoll_updates;

template <typename T, typename Func>
TypeErasedCallback get_erased_callback(Func && callback)
{
  return [callback = std::forward<Func>(callback)](AnyObject && arg) {
    if (typeid(T) == arg.type()) {
      auto && typed_arg = static_cast<TypedMessagePtr<T> &&>(arg);
      callback(std::move(typed_arg).get());
    } else {
      RCLCPP_ERROR(
        logger, "Agnocast internal implementation error: bad allocation when callback is called");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  };
}

template <typename MessageT, typename Func>
uint32_t register_callback(
  Func && callback, const std::string & topic_name, const topic_local_id_t subscriber_id,
  const bool is_transient_local, mqd_t mqdes, const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  // NOTE: ipc_shared_ptr<MessageT> and ipc_shared_ptr<MessageT>&& make no difference in the
  // assertion expression below, but we go with ipc_shared_ptr<MessageT>&&.
  static_assert(
    std::is_invocable_v<std::decay_t<Func>, agnocast::ipc_shared_ptr<MessageT> &&>,
    "Callback must be callable with ipc_shared_ptr (const&, &&, or by-value)");

  TypeErasedCallback erased_callback = get_erased_callback<MessageT>(std::forward<Func>(callback));

  auto message_creator = [](
                           const void * ptr, const std::string & topic_name,
                           const topic_local_id_t subscriber_id, const int64_t entry_id) {
    return std::make_unique<TypedMessagePtr<MessageT>>(agnocast::ipc_shared_ptr<MessageT>(
      const_cast<MessageT *>(static_cast<const MessageT *>(ptr)), topic_name, subscriber_id,
      entry_id));
  };

  uint32_t executable_id = next_executable_id.fetch_add(1);

  {
    std::lock_guard<std::mutex> lock(id2_executable_info_mtx);
    id2_executable_info[executable_id] = ExecutableInfo{
      ExecutableInfo::Type::Subscription,
      callback_group,
      true,  // need_epoll_update
      mqdes,
      topic_name,
      subscriber_id,
      is_transient_local,
      erased_callback,
      message_creator,
      {},   // timer_callback (unused)
      {},   // next_call_time (unused)
      {}};  // period (unused)
  }

  need_epoll_updates.store(true);

  return executable_id;
}

int create_timer_fd(std::chrono::nanoseconds period);

void handle_timer_event(ExecutableInfo & executable_info);

uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group);

void receive_message(
  [[maybe_unused]] const uint32_t executable_id,  // for CARET
  [[maybe_unused]] const pid_t my_pid,            // for CARET
  const ExecutableInfo & executable_info, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables);

void wait_and_handle_epoll_event(
  const int epoll_fd, const pid_t my_pid, const int timeout_ms,
  std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables);

template <class ValidateFn>
void prepare_epoll_impl(
  const int epoll_fd, const pid_t my_pid, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables,
  ValidateFn && validate_callback_group)
{
  std::lock_guard<std::mutex> lock(id2_executable_info_mtx);

  for (auto & it : id2_executable_info) {
    const uint32_t executable_id = it.first;
    ExecutableInfo & executable_info = it.second;

    if (!executable_info.need_epoll_update) {
      continue;
    }

    if (!validate_callback_group(executable_info.callback_group)) {
      continue;
    }

    struct epoll_event ev = {};
    ev.events = EPOLLIN;
    ev.data.u32 = executable_id;

    if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, executable_info.fd, &ev) == -1) {
      RCLCPP_ERROR(logger, "epoll_ctl failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    if (
      executable_info.type == ExecutableInfo::Type::Subscription &&
      executable_info.is_transient_local) {
      agnocast::receive_message(
        executable_id, my_pid, executable_info, ready_agnocast_executables_mutex,
        ready_agnocast_executables);
    }

    executable_info.need_epoll_update = false;
  }

  const bool all_updated = std::none_of(
    id2_executable_info.begin(), id2_executable_info.end(),
    [](const auto & it) { return it.second.need_epoll_update; });

  if (all_updated) {
    need_epoll_updates.store(false);
  }
}

}  // namespace agnocast

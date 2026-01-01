#include "agnocast/agnocast_callback_info.hpp"

#include "agnocast/agnocast.hpp"

#include <sys/timerfd.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <stdexcept>

namespace agnocast
{

std::mutex id2_executable_info_mtx;
const int executable_map_bkt_cnt = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, ExecutableInfo> id2_executable_info(executable_map_bkt_cnt);
std::atomic<uint32_t> next_executable_id{0};
std::atomic<bool> need_epoll_updates{false};

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

void handle_timer_event(ExecutableInfo & executable_info)
{
  // Read the number of expirations to clear the event
  uint64_t expirations = 0;
  const ssize_t ret = read(executable_info.fd, &expirations, sizeof(expirations));

  if (ret == -1) {
    if (errno != EAGAIN && errno != EWOULDBLOCK) {
      return;
    }
  }

  if (expirations > 0) {
    const auto actual_call_time = std::chrono::steady_clock::now();
    TimerCallbackInfo callback_info{executable_info.next_call_time, actual_call_time};

    executable_info.timer_callback(callback_info);

    // Update next expected call time
    executable_info.next_call_time += executable_info.period;
  }
}

uint32_t register_timer(
  std::function<void(TimerCallbackInfo &)> callback, std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  const int timer_fd = create_timer_fd(period);
  const uint32_t executable_id = next_executable_id.fetch_add(1);
  const auto now = std::chrono::steady_clock::now();

  {
    std::lock_guard<std::mutex> lock(id2_executable_info_mtx);
    id2_executable_info[executable_id] = ExecutableInfo{
      ExecutableInfo::Type::Timer,
      callback_group,
      true,  // need_epoll_update
      timer_fd,
      {},     // topic_name (unused)
      {},     // subscriber_id (unused)
      false,  // is_transient_local (unused)
      {},     // subscription_callback (unused)
      {},     // message_creator (unused)
      std::move(callback),
      now + period,  // next_call_time
      period};
  }

  need_epoll_updates.store(true);

  return executable_id;
}

void receive_message(
  [[maybe_unused]] const uint32_t executable_id,  // for CARET
  [[maybe_unused]] const pid_t my_pid,            // for CARET
  const ExecutableInfo & executable_info, std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables)
{
  union ioctl_receive_msg_args receive_args = {};
  receive_args.topic_name = {executable_info.topic_name.c_str(), executable_info.topic_name.size()};
  receive_args.subscriber_id = executable_info.subscriber_id;

  {
    std::lock_guard<std::mutex> lock(mmap_mtx);

    if (ioctl(agnocast_fd, AGNOCAST_RECEIVE_MSG_CMD, &receive_args) < 0) {
      RCLCPP_ERROR(logger, "AGNOCAST_RECEIVE_MSG_CMD failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    // Map the shared memory region with read permissions whenever a new publisher is discovered.
    for (uint32_t i = 0; i < receive_args.ret_pub_shm_info.publisher_num; i++) {
      const pid_t pid = receive_args.ret_pub_shm_info.publisher_pids[i];
      const uint64_t addr = receive_args.ret_pub_shm_info.shm_addrs[i];
      const uint64_t size = receive_args.ret_pub_shm_info.shm_sizes[i];
      map_read_only_area(pid, addr, size);
    }
  }

  // older messages first
  for (int32_t i = static_cast<int32_t>(receive_args.ret_entry_num) - 1; i >= 0; i--) {
    const std::shared_ptr<std::function<void()>> callable =
      std::make_shared<std::function<void()>>([executable_info, receive_args, i]() {
        auto typed_msg = executable_info.message_creator(
          reinterpret_cast<void *>(receive_args.ret_entry_addrs[i]), executable_info.topic_name,
          executable_info.subscriber_id, receive_args.ret_entry_ids[i]);
        executable_info.subscription_callback(std::move(*typed_msg));
      });

    {
      constexpr uint8_t PID_SHIFT_BITS = 32;
      uint64_t pid_executable_id =
        (static_cast<uint64_t>(my_pid) << PID_SHIFT_BITS) | executable_id;
      TRACEPOINT(
        agnocast_create_callable, static_cast<const void *>(callable.get()),
        receive_args.ret_entry_ids[i], pid_executable_id);
    }

    {
      std::lock_guard<std::mutex> ready_lock{ready_agnocast_executables_mutex};
      ready_agnocast_executables.emplace_back(
        AgnocastExecutable{callable, executable_info.callback_group});
    }
  }
}

void wait_and_handle_epoll_event(
  const int epoll_fd, const pid_t my_pid, const int timeout_ms,
  std::mutex & ready_agnocast_executables_mutex,
  std::vector<AgnocastExecutable> & ready_agnocast_executables)
{
  struct epoll_event event = {};

  // blocking with timeout
  const int nfds = epoll_wait(epoll_fd, &event, 1 /*maxevents*/, timeout_ms);

  if (nfds == -1) {
    if (errno != EINTR) {  // signal handler interruption is not error
      RCLCPP_ERROR(logger, "epoll_wait failed: %s", strerror(errno));
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }

    return;
  }

  // timeout
  if (nfds == 0) {
    return;
  }

  const uint32_t executable_id = event.data.u32;
  ExecutableInfo executable_info;
  ExecutableInfo::Type type;

  {
    std::lock_guard<std::mutex> lock(id2_executable_info_mtx);
    const auto it = id2_executable_info.find(executable_id);
    if (it == id2_executable_info.end()) {
      RCLCPP_ERROR(
        logger, "Agnocast internal implementation error: executable info cannot be found");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
    type = it->second.type;
    executable_info = it->second;
  }

  if (type == ExecutableInfo::Type::Timer) {
    // Create a callable that handles the timer event
    const std::shared_ptr<std::function<void()>> callable =
      std::make_shared<std::function<void()>>([executable_id]() {
        std::lock_guard<std::mutex> lock(id2_executable_info_mtx);
        auto it = id2_executable_info.find(executable_id);
        if (it != id2_executable_info.end()) {
          handle_timer_event(it->second);
        }
      });

    {
      std::lock_guard<std::mutex> ready_lock{ready_agnocast_executables_mutex};
      ready_agnocast_executables.emplace_back(
        AgnocastExecutable{callable, executable_info.callback_group});
    }
  } else {
    // Handle subscription callback
    MqMsgAgnocast mq_msg = {};

    // non-blocking
    auto ret =
      mq_receive(executable_info.fd, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), nullptr);
    if (ret < 0) {
      if (errno != EAGAIN) {
        RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      return;
    }

    agnocast::receive_message(
      executable_id, my_pid, executable_info, ready_agnocast_executables_mutex,
      ready_agnocast_executables);
  }
}

std::vector<std::string> get_agnocast_topics_by_group(
  const rclcpp::CallbackGroup::SharedPtr & group)
{
  std::vector<std::string> topic_names;

  {
    std::lock_guard<std::mutex> lock(id2_executable_info_mtx);
    for (const auto & [id, executable_info] : id2_executable_info) {
      if (
        executable_info.type == ExecutableInfo::Type::Subscription &&
        executable_info.callback_group == group) {
        topic_names.push_back(executable_info.topic_name);
      }
    }
  }

  std::sort(topic_names.begin(), topic_names.end());

  return topic_names;
}

}  // namespace agnocast

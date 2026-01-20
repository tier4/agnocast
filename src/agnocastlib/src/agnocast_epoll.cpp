#include "agnocast/agnocast_epoll.hpp"

#include "agnocast/agnocast.hpp"

namespace agnocast
{

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

  const uint32_t event_id = event.data.u32;

  if (event_id & TIMER_EVENT_FLAG) {
    // Timer event
    const uint32_t timer_id = event_id & ~TIMER_EVENT_FLAG;
    rclcpp::CallbackGroup::SharedPtr callback_group;

    {
      std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
      const auto it = id2_timer_info.find(timer_id);
      if (it == id2_timer_info.end()) {
        RCLCPP_ERROR(logger, "Agnocast internal implementation error: timer info cannot be found");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }
      callback_group = it->second.callback_group;
    }

    // Create a callable that handles the timer event
    const std::shared_ptr<std::function<void()>> callable =
      std::make_shared<std::function<void()>>([timer_id]() {
        std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
        auto it = id2_timer_info.find(timer_id);
        if (it != id2_timer_info.end()) {
          handle_timer_event(it->second);
        }
      });

    {
      std::lock_guard<std::mutex> ready_lock{ready_agnocast_executables_mutex};
      ready_agnocast_executables.emplace_back(AgnocastExecutable{callable, callback_group});
    }
  } else {
    // Subscription event
    const uint32_t subscription_id = event_id & ~SUBSCRIPTION_EVENT_FLAG;
    SubscriptionInfo subscription_info;

    {
      std::lock_guard<std::mutex> lock(id2_subscription_info_mtx);

      const auto it = id2_subscription_info.find(subscription_id);
      if (it == id2_subscription_info.end()) {
        RCLCPP_ERROR(
          logger, "Agnocast internal implementation error: subscription info cannot be found");
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      subscription_info = it->second;
    }

    MqMsgAgnocast mq_msg = {};

    // non-blocking
    auto ret = mq_receive(
      subscription_info.mqdes, reinterpret_cast<char *>(&mq_msg), sizeof(mq_msg), nullptr);
    if (ret < 0) {
      if (errno != EAGAIN) {
        RCLCPP_ERROR(logger, "mq_receive failed: %s", strerror(errno));
        close(agnocast_fd);
        exit(EXIT_FAILURE);
      }

      return;
    }

    agnocast::receive_message(
      subscription_id, my_pid, subscription_info, ready_agnocast_executables_mutex,
      ready_agnocast_executables);
  }
}

}  // namespace agnocast

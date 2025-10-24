#include "agnocast/agnocast_client.hpp"

#include "agnocast/agnocast_ioctl.hpp"

#include <chrono>
#include <memory>

namespace agnocast
{

uint32_t get_agnocast_sub_count(const std::string & topic_name)
{
  auto topic_info_buffer = std::make_unique<topic_info_ret[]>(MAX_TOPIC_INFO_RET_NUM);

  ioctl_topic_info_args topic_info_args = {};
  topic_info_args.topic_name = {topic_name.c_str(), topic_name.size()};
  topic_info_args.topic_info_ret_buffer_addr = reinterpret_cast<uint64_t>(topic_info_buffer.get());
  if (ioctl(agnocast_fd, AGNOCAST_GET_TOPIC_SUBSCRIBER_INFO_CMD, &topic_info_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_TOPIC_SUBSCRIBER_INFO_CMD failed: %s", strerror(errno));
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  return topic_info_args.ret_topic_info_ret_num;
}

bool service_is_ready_core(const std::string & service_name)
{
  uint32_t sub_count = get_agnocast_sub_count(create_service_request_topic_name(service_name));

  if (sub_count == 0) {
    return false;
  } else {
    if (sub_count > 1) {
      RCLCPP_WARN(
        logger, "Multiple services with the same name found (name=%s).", service_name.c_str());
    }
    return true;
  }
}

bool wait_for_service_nanoseconds(
  rclcpp::Context::SharedPtr context, const std::string & service_name,
  std::chrono::nanoseconds timeout)
{
  auto start = std::chrono::steady_clock::now();
  if (service_is_ready_core(service_name)) {
    return true;
  }
  if (timeout == std::chrono::nanoseconds(0)) {
    // non-blocking, return immediately
    return false;
  }
  // If timeout is negative, wait indefinitely.
  std::chrono::nanoseconds time_to_wait = timeout > std::chrono::nanoseconds(0)
                                            ? timeout - (std::chrono::steady_clock::now() - start)
                                            : std::chrono::nanoseconds::max();
  do {
    if (!rclcpp::ok(context)) {
      return false;
    }
    auto interval = std::min(time_to_wait, std::chrono::nanoseconds(100 * 1000 * 1000) /*100ms*/);
    std::this_thread::sleep_for(interval);
    if (service_is_ready_core(service_name)) {
      return true;
    }
    if (timeout > std::chrono::nanoseconds(0)) {
      time_to_wait = timeout - (std::chrono::steady_clock::now() - start);
    }
    // If timeout is negative, time_to_wait will never reach zero.
  } while (time_to_wait > std::chrono::nanoseconds(0));
  return false;
}

}  // namespace agnocast

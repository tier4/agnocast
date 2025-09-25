#include "agnocast/agnocast_client.hpp"

#include "agnocast/agnocast_ioctl.hpp"

#include <chrono>

namespace agnocast
{

struct topic_info_ret * get_agnocast_sub_nodes(
  const std::string & topic_name, int & topic_info_ret_count)
{
  topic_info_ret_count = 0;

  struct topic_info_ret * agnocast_topic_info_ret_buffer = static_cast<struct topic_info_ret *>(
    malloc(MAX_TOPIC_INFO_RET_NUM * sizeof(struct topic_info_ret)));

  if (agnocast_topic_info_ret_buffer == nullptr) {
    RCLCPP_ERROR(logger, "Memory allocation failed\n");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  union ioctl_topic_info_args topic_info_args = {};
  topic_info_args.topic_name = {topic_name.c_str(), topic_name.size()};
  topic_info_args.topic_info_ret_buffer_addr =
    reinterpret_cast<uint64_t>(agnocast_topic_info_ret_buffer);
  if (ioctl(agnocast_fd, AGNOCAST_GET_TOPIC_SUBSCRIBER_INFO_CMD, &topic_info_args) < 0) {
    RCLCPP_ERROR(logger, "AGNOCAST_GET_TOPIC_SUBSCRIBER_INFO_CMD failed: %s", strerror(errno));
    free(agnocast_topic_info_ret_buffer);
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  if (topic_info_args.ret_topic_info_ret_num == 0) {
    free(agnocast_topic_info_ret_buffer);
    return nullptr;
  }

  topic_info_ret_count = static_cast<int>(topic_info_args.ret_topic_info_ret_num);
  return agnocast_topic_info_ret_buffer;
}

bool service_is_ready_core(const std::string & service_name)
{
  int sub_count;
  struct topic_info_ret * sub_nodes =
    get_agnocast_sub_nodes(create_service_request_topic_name(service_name), sub_count);

  if (sub_count == 0) {
    return false;
  } else {
    if (sub_count > 1) {
      RCLCPP_WARN(
        logger, "Multiple services with the same name found (name=%s).", service_name.c_str());
    }
    free(sub_nodes);
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

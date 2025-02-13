#include "agnocast_utils.hpp"

#include <cstring>
#include <sstream>
#include <thread>

namespace agnocast
{

extern int agnocast_fd;

rclcpp::Logger logger = rclcpp::get_logger("Agnocast");

void validate_ld_preload()
{
  const char * ld_preload = getenv("LD_PRELOAD");
  if (
    ld_preload == nullptr || (std::strstr(ld_preload, "libagnocast_heaphook.so:") == nullptr &&
                              std::strstr(ld_preload, ":libagnocast_heaphook.so") == nullptr)) {
    RCLCPP_ERROR(logger, "LD_PRELOAD is not set to `libagnocast_heaphook.so:$LD_PRELOAD`");
    exit(EXIT_FAILURE);
  }
}

static std::string create_mq_name(
  const std::string & header, const std::string & topic_name, const topic_local_id_t id)
{
  if (topic_name.length() == 0 || topic_name[0] != '/') {
    RCLCPP_ERROR(logger, "create_mq_name failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  std::string mq_name = topic_name;
  mq_name[0] = '@';
  mq_name = header + mq_name + "@" + std::to_string(id);

  // As a mq_name, '/' cannot be used
  for (size_t i = 1; i < mq_name.size(); i++) {
    if (mq_name[i] == '/') {
      mq_name[i] = '_';
    }
  }

  return mq_name;
}

std::string create_mq_name_for_agnocast_publish(
  const std::string & topic_name, const topic_local_id_t id)
{
  return create_mq_name("/agnocast", topic_name, id);
}

std::string create_mq_name_for_ros2_publish(
  const std::string & topic_name, const topic_local_id_t id)
{
  return create_mq_name("/agnocast_to_ros2", topic_name, id);
}

std::string create_shm_name(const pid_t pid)
{
  return "/agnocast@" + std::to_string(pid);
}

uint64_t agnocast_get_timestamp()
{
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

}  // namespace agnocast

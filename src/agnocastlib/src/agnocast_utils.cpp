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

std::string create_mq_name(const std::string & topic_name, const std::string & id)
{
  std::string mq_name = topic_name + "@" + id;

  if (mq_name[0] != '/') {
    RCLCPP_ERROR(logger, "create_mq_name failed");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  // As a mq_name, '/' cannot be used
  for (size_t i = 1; i < mq_name.size(); i++) {
    if (mq_name[i] == '/') {
      mq_name[i] = '_';
    }
  }

  return mq_name;
}

std::string create_mq_name(const std::string & topic_name, const std::thread::id tid)
{
  std::stringstream ss;
  ss << tid;
  return create_mq_name(topic_name, "thread_" + ss.str());
}

std::string create_mq_name(const std::string & topic_name, const topic_local_id_t id)
{
  return create_mq_name(topic_name, std::to_string(id));
}

std::string create_shm_name(const pid_t pid)
{
  return "/agnocast@" + std::to_string(pid);
}

std::string create_mq_name_new_publisher(const pid_t pid)
{
  return "/new_publisher@" + std::to_string(pid);
}

uint64_t agnocast_get_timestamp()
{
  auto now = std::chrono::system_clock::now();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
}

}  // namespace agnocast

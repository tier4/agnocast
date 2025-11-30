#include "agnocast/agnocast_bridge_utils.hpp"

#include "agnocast/agnocast_ioctl.hpp"

namespace agnocast
{

void safe_strncpy(char * dest, const char * src, size_t dest_size)
{
  if (dest_size == 0) return;
  if (src == nullptr) {
    dest[0] = '\0';
    return;
  }
  std::strncpy(dest, src, dest_size - 1);
  dest[dest_size - 1] = '\0';
}

void unregister_bridge(pid_t pid, const char * topic_name)
{
  struct ioctl_bridge_args unreg_args = {};
  unreg_args.pid = pid;
  safe_strncpy(unreg_args.topic_name, topic_name, MAX_TOPIC_NAME_LEN);

  if (ioctl(agnocast_fd, AGNOCAST_UNREGISTER_BRIDGE_CMD, &unreg_args) < 0) {
    if (errno != ENOENT) {
      std::cerr << "[Agnocast] AGNOCAST_UNREGISTER_BRIDGE_CMD failed: " << strerror(errno)
                << std::endl;

      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  }
}

}  // namespace agnocast
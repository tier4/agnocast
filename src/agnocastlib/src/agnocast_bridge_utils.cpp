#include "agnocast/agnocast_bridge_utils.hpp"

#include <cstring>

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

}  // namespace agnocast

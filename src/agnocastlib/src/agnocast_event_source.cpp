#include "agnocast/agnocast_event_source.hpp"

namespace agnocast
{

std::atomic<bool> need_epoll_updates{false};

}  // namespace agnocast

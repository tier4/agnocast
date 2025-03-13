#include "agnocast/agnocast_callback_info.hpp"

namespace agnocast
{

std::mutex id2_callback_info_mtx;
static const int CALLBACK_MAP_BKT_CNT = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, CallbackInfo> id2_callback_info(CALLBACK_MAP_BKT_CNT);
std::atomic<bool> need_epoll_updates{false};

}  // namespace agnocast
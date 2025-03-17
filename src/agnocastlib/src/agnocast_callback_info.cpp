#include "agnocast/agnocast_callback_info.hpp"

namespace agnocast
{

std::mutex id2_callback_info_mtx;
const int callback_map_bkt_cnt = 100;  // arbitrary size to prevent rehash
std::unordered_map<uint32_t, CallbackInfo> id2_callback_info(callback_map_bkt_cnt);
std::atomic<bool> need_epoll_updates{false};

}  // namespace agnocast

#include "agnocast/agnocast_callback_info.hpp"

namespace agnocast
{

// Backward compatibility: reference aliases to new names
std::mutex & id2_callback_info_mtx = id2_subscription_info_mtx;
std::unordered_map<uint32_t, CallbackInfo> & id2_callback_info = id2_subscription_info;
std::atomic<uint32_t> & next_callback_info_id = next_subscription_id;

}  // namespace agnocast

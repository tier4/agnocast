#pragma once

// This file provides backward compatibility for code using the old callback_info names.
// New code should use agnocast_subscription_info.hpp and agnocast_epoll.hpp directly.

#include "agnocast/agnocast_epoll.hpp"
#include "agnocast/agnocast_subscription_info.hpp"

namespace agnocast
{

// Backward compatibility aliases
using CallbackInfo = SubscriptionInfo;

extern std::mutex & id2_callback_info_mtx;
extern std::unordered_map<uint32_t, CallbackInfo> & id2_callback_info;
extern std::atomic<uint32_t> & next_callback_info_id;

// Backward compatibility function template
template <typename MessageT, typename Func>
uint32_t register_callback(
  Func && callback, const std::string & topic_name, const topic_local_id_t subscriber_id,
  const bool is_transient_local, mqd_t mqdes, const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  return register_subscription<MessageT>(
    std::forward<Func>(callback), topic_name, subscriber_id, is_transient_local, mqdes,
    callback_group);
}

}  // namespace agnocast

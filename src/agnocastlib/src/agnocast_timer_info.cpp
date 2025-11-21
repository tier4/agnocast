// Copyright 2025 Agnocast
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "agnocast/agnocast_timer_info.hpp"
#include "agnocast/agnocast_callback_info.hpp"

namespace agnocast
{

std::mutex id2_timer_info_mtx;
std::unordered_map<uint32_t, TimerInfo> id2_timer_info;
std::atomic<uint32_t> next_timer_id{0};

uint32_t register_timer(
  std::function<void()> callback,
  std::chrono::nanoseconds period,
  const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  auto timer = std::make_shared<AgnocastTimer>(period, std::move(callback));
  const uint32_t timer_id = next_timer_id.fetch_add(1);

  {
    std::lock_guard<std::mutex> lock(id2_timer_info_mtx);
    id2_timer_info[timer_id] = TimerInfo{
      timer,
      timer->get_fd(),
      callback_group,
      true  // need_epoll_update
    };
  }

  need_epoll_updates.store(true);

  return timer_id;
}

}  // namespace agnocast

// Copyright 2025 The Agnocast Authors.
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

#include "agnocast/agnocast_timer.hpp"

#include "agnocast/agnocast_timer_info.hpp"

#include <stdexcept>

namespace agnocast
{

TimerBase::~TimerBase()
{
  unregister_timer_info(timer_id_);
}

void TimerBase::cancel()
{
  // TODO(Koichi98): Implement cancel functionality
  throw std::runtime_error("TimerBase::cancel() is not implemented");
}

bool TimerBase::is_canceled() const
{
  // TODO(Koichi98): Implement is_canceled functionality
  throw std::runtime_error("TimerBase::is_canceled() is not implemented");
}

void TimerBase::reset()
{
  // TODO(Koichi98): Implement reset functionality
  throw std::runtime_error("TimerBase::reset() is not implemented");
}

std::chrono::nanoseconds TimerBase::time_until_trigger() const
{
  // TODO(Koichi98): Implement time_until_trigger functionality
  throw std::runtime_error("TimerBase::time_until_trigger() is not implemented");
}

}  // namespace agnocast

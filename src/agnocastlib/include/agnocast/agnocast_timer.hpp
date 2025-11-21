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

#ifndef AGNOCAST__AGNOCAST_TIMER_HPP_
#define AGNOCAST__AGNOCAST_TIMER_HPP_

#include <chrono>
#include <functional>
#include <stdexcept>

namespace agnocast
{

class AgnocastTimer
{
public:
  /**
   * @brief Construct a new Agnocast Timer object
   *
   * @param period Timer period in nanoseconds
   * @param callback Function to call when timer expires
   * @throws std::runtime_error if timer creation fails
   */
  AgnocastTimer(std::chrono::nanoseconds period, std::function<void()> callback);

  /**
   * @brief Destroy the Agnocast Timer object
   */
  ~AgnocastTimer();

  // Disable copy and move
  AgnocastTimer(const AgnocastTimer &) = delete;
  AgnocastTimer & operator=(const AgnocastTimer &) = delete;
  AgnocastTimer(AgnocastTimer &&) = delete;
  AgnocastTimer & operator=(AgnocastTimer &&) = delete;

  /**
   * @brief Get the file descriptor for this timer
   *
   * @return int Timer file descriptor
   */
  int get_fd() const;

  /**
   * @brief Handle a timer event (read expiration count and execute callback)
   */
  void handle_event();

  /**
   * @brief Cancel the timer
   */
  void cancel();

  /**
   * @brief Check if timer is canceled
   *
   * @return true if canceled
   */
  bool is_canceled() const;

  /**
   * @brief Reset the timer with a new period
   *
   * @param period New timer period in nanoseconds
   * @throws std::runtime_error if timer update fails
   */
  void reset(std::chrono::nanoseconds period);

private:
  int timer_fd_;
  std::function<void()> callback_;
  bool canceled_;
};

}  // namespace agnocast

#endif  // AGNOCAST__AGNOCAST_TIMER_HPP_

#pragma once

#include "rclcpp/callback_group.hpp"
#include "rclcpp/clock.hpp"
#include "rclcpp/macros.hpp"

#include <atomic>
#include <chrono>
#include <functional>
#include <memory>
#include <type_traits>

namespace agnocast
{

class TimerBase
{
public:
  RCLCPP_SMART_PTR_DEFINITIONS_NOT_COPYABLE(TimerBase)

  virtual ~TimerBase() = default;

  void cancel();

  bool is_canceled() const;

  void reset();

  std::chrono::nanoseconds time_until_trigger() const;

  virtual bool is_steady() const { return true; }

  virtual rclcpp::Clock::SharedPtr get_clock() const { return nullptr; }

  virtual void execute_callback() = 0;

  rclcpp::CallbackGroup::SharedPtr get_callback_group() const { return callback_group_; }

  uint32_t get_timer_id() const { return timer_id_; }

protected:
  TimerBase(
    uint32_t timer_id, std::chrono::nanoseconds period,
    rclcpp::CallbackGroup::SharedPtr callback_group)
  : timer_id_(timer_id), period_(period), callback_group_(std::move(callback_group))
  {
  }

  uint32_t timer_id_;
  std::chrono::nanoseconds period_;
  rclcpp::CallbackGroup::SharedPtr callback_group_;
  std::atomic<bool> canceled_{false};
};

template <typename FunctorT>
class WallTimer : public TimerBase
{
public:
  RCLCPP_SMART_PTR_DEFINITIONS(WallTimer)

  WallTimer(
    uint32_t timer_id, std::chrono::nanoseconds period,
    rclcpp::CallbackGroup::SharedPtr callback_group, FunctorT && callback)
  : TimerBase(timer_id, period, std::move(callback_group)),
    callback_(std::forward<FunctorT>(callback))
  {
  }

  void execute_callback() override
  {
    if constexpr (std::is_invocable_v<FunctorT, TimerBase &>) {
      callback_(*this);
    } else {
      callback_();
    }
  }

protected:
  RCLCPP_DISABLE_COPY(WallTimer)

  FunctorT callback_;
};

template <typename FunctorT>
class GenericTimer : public TimerBase
{
public:
  RCLCPP_SMART_PTR_DEFINITIONS(GenericTimer)

  GenericTimer(
    uint32_t timer_id, std::chrono::nanoseconds period,
    rclcpp::CallbackGroup::SharedPtr callback_group, rclcpp::Clock::SharedPtr clock,
    FunctorT && callback)
  : TimerBase(timer_id, period, std::move(callback_group)),
    clock_(std::move(clock)),
    callback_(std::forward<FunctorT>(callback))
  {
  }

  void execute_callback() override
  {
    if constexpr (std::is_invocable_v<FunctorT, TimerBase &>) {
      callback_(*this);
    } else {
      callback_();
    }
  }

  bool is_steady() const override
  {
    return clock_ ? (clock_->get_clock_type() == RCL_STEADY_TIME) : true;
  }

  rclcpp::Clock::SharedPtr get_clock() const override { return clock_; }

protected:
  RCLCPP_DISABLE_COPY(GenericTimer)

  rclcpp::Clock::SharedPtr clock_;
  FunctorT callback_;
};

}  // namespace agnocast

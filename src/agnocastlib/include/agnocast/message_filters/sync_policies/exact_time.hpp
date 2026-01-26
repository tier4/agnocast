// Copyright 2025 The Autoware Contributors
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "agnocast/message_filters/synchronizer.hpp"

#include <rclcpp/rclcpp.hpp>

#include <message_filters/connection.h>
#include <message_filters/message_traits.h>
#include <message_filters/null_types.h>

#include <map>
#include <mutex>
#include <tuple>

namespace agnocast
{
namespace message_filters
{
namespace sync_policies
{

using ::message_filters::Connection;
using ::message_filters::NullType;

template <
  typename M0, typename M1, typename M2 = NullType, typename M3 = NullType, typename M4 = NullType,
  typename M5 = NullType, typename M6 = NullType, typename M7 = NullType, typename M8 = NullType>
class ExactTime : public PolicyBase<M0, M1, M2, M3, M4, M5, M6, M7, M8>
{
public:
  using Sync = Synchronizer<ExactTime>;
  using Super = PolicyBase<M0, M1, M2, M3, M4, M5, M6, M7, M8>;
  using typename Super::Events;
  using typename Super::M0Event;
  using typename Super::M1Event;
  using typename Super::M2Event;
  using typename Super::M3Event;
  using typename Super::M4Event;
  using typename Super::M5Event;
  using typename Super::M6Event;
  using typename Super::M7Event;
  using typename Super::M8Event;
  using typename Super::Messages;
  using typename Super::RealTypeCount;
  using typename Super::Signal;
  using Tuple = Events;

  explicit ExactTime(uint32_t queue_size) : parent_(nullptr), queue_size_(queue_size) {}

  ExactTime(const ExactTime & e) { *this = e; }

  ExactTime & operator=(const ExactTime & rhs)
  {
    parent_ = rhs.parent_;
    queue_size_ = rhs.queue_size_;
    last_signal_time_ = rhs.last_signal_time_;
    tuples_ = rhs.tuples_;

    return *this;
  }

  void initParent(Sync * parent) { parent_ = parent; }

  template <int i>
  void add(const typename std::tuple_element<i, Events>::type & evt)
  {
    if (!evt) return;
    RCUTILS_ASSERT(parent_);

    namespace mt = ::message_filters::message_traits;

    std::lock_guard<std::mutex> lock(mutex_);

    Tuple & t = tuples_[mt::TimeStamp<typename std::tuple_element<i, Messages>::type>::value(*evt)];
    std::get<i>(t) = evt;

    checkTuple(t);
  }

  template <typename C>
  Connection registerDropCallback(const C & callback)
  {
    return drop_signal_.addCallback(callback);
  }

  template <typename C>
  Connection registerDropCallback(C & callback)
  {
    return drop_signal_.addCallback(callback);
  }

  template <typename C, typename T>
  Connection registerDropCallback(const C & callback, T * t)
  {
    return drop_signal_.addCallback(callback, t);
  }

  template <typename C, typename T>
  Connection registerDropCallback(C & callback, T * t)
  {
    return drop_signal_.addCallback(callback, t);
  }

private:
  // assumes mutex_ is already locked
  void checkTuple(Tuple & t)
  {
    namespace mt = ::message_filters::message_traits;

    bool full = true;
    full = full && static_cast<bool>(std::get<0>(t));
    full = full && static_cast<bool>(std::get<1>(t));
    full = full && (RealTypeCount::value > 2 ? static_cast<bool>(std::get<2>(t)) : true);
    full = full && (RealTypeCount::value > 3 ? static_cast<bool>(std::get<3>(t)) : true);
    full = full && (RealTypeCount::value > 4 ? static_cast<bool>(std::get<4>(t)) : true);
    full = full && (RealTypeCount::value > 5 ? static_cast<bool>(std::get<5>(t)) : true);
    full = full && (RealTypeCount::value > 6 ? static_cast<bool>(std::get<6>(t)) : true);
    full = full && (RealTypeCount::value > 7 ? static_cast<bool>(std::get<7>(t)) : true);
    full = full && (RealTypeCount::value > 8 ? static_cast<bool>(std::get<8>(t)) : true);

    if (full) {
      parent_->signal(
        std::get<0>(t), std::get<1>(t), std::get<2>(t), std::get<3>(t), std::get<4>(t),
        std::get<5>(t), std::get<6>(t), std::get<7>(t), std::get<8>(t));

      last_signal_time_ = mt::TimeStamp<M0>::value(*std::get<0>(t));

      tuples_.erase(last_signal_time_);

      clearOldTuples();
    }

    if (queue_size_ > 0) {
      while (tuples_.size() > queue_size_) {
        Tuple & t2 = tuples_.begin()->second;
        drop_signal_.call(
          std::get<0>(t2), std::get<1>(t2), std::get<2>(t2), std::get<3>(t2), std::get<4>(t2),
          std::get<5>(t2), std::get<6>(t2), std::get<7>(t2), std::get<8>(t2));
        tuples_.erase(tuples_.begin());
      }
    }
  }

  // assumes mutex_ is already locked
  void clearOldTuples()
  {
    typename M_TimeToTuple::iterator it = tuples_.begin();
    typename M_TimeToTuple::iterator end = tuples_.end();
    for (; it != end;) {
      if (it->first <= last_signal_time_) {
        typename M_TimeToTuple::iterator old = it;
        ++it;

        Tuple & t = old->second;
        drop_signal_.call(
          std::get<0>(t), std::get<1>(t), std::get<2>(t), std::get<3>(t), std::get<4>(t),
          std::get<5>(t), std::get<6>(t), std::get<7>(t), std::get<8>(t));
        tuples_.erase(old);
      } else {
        // the map is sorted by time, so we can ignore anything after this if this one's time is ok
        break;
      }
    }
  }

  Sync * parent_;
  uint32_t queue_size_;
  using M_TimeToTuple = std::map<rclcpp::Time, Tuple>;
  M_TimeToTuple tuples_;
  rclcpp::Time last_signal_time_;
  Signal drop_signal_;
  mutable std::mutex mutex_;
};

}  // namespace sync_policies
}  // namespace message_filters
}  // namespace agnocast

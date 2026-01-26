// Copyright 2025 The Autoware Contributors
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "agnocast/agnocast_smart_pointer.hpp"

#include <message_filters/connection.h>
#include <message_filters/null_types.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <mutex>
#include <vector>

namespace agnocast
{
namespace message_filters
{

using ::message_filters::Connection;
using ::message_filters::NullType;

template <
  typename M0, typename M1, typename M2, typename M3, typename M4, typename M5, typename M6,
  typename M7, typename M8>
class CallbackHelper9
{
public:
  using M0Event = ipc_shared_ptr<const M0>;
  using M1Event = ipc_shared_ptr<const M1>;
  using M2Event = ipc_shared_ptr<const M2>;
  using M3Event = ipc_shared_ptr<const M3>;
  using M4Event = ipc_shared_ptr<const M4>;
  using M5Event = ipc_shared_ptr<const M5>;
  using M6Event = ipc_shared_ptr<const M6>;
  using M7Event = ipc_shared_ptr<const M7>;
  using M8Event = ipc_shared_ptr<const M8>;

  virtual ~CallbackHelper9() {}

  virtual void call(
    const M0Event & e0, const M1Event & e1, const M2Event & e2, const M3Event & e3,
    const M4Event & e4, const M5Event & e5, const M6Event & e6, const M7Event & e7,
    const M8Event & e8) = 0;

  using Ptr = std::shared_ptr<CallbackHelper9>;
};

template <
  typename P0, typename P1, typename P2, typename P3, typename P4, typename P5, typename P6,
  typename P7, typename P8, typename M0, typename M1, typename M2, typename M3, typename M4,
  typename M5, typename M6, typename M7, typename M8>
class CallbackHelper9T : public CallbackHelper9<M0, M1, M2, M3, M4, M5, M6, M7, M8>
{
public:
  using Base = CallbackHelper9<M0, M1, M2, M3, M4, M5, M6, M7, M8>;
  using typename Base::M0Event;
  using typename Base::M1Event;
  using typename Base::M2Event;
  using typename Base::M3Event;
  using typename Base::M4Event;
  using typename Base::M5Event;
  using typename Base::M6Event;
  using typename Base::M7Event;
  using typename Base::M8Event;
  using Callback = std::function<void(P0, P1, P2, P3, P4, P5, P6, P7, P8)>;

  CallbackHelper9T(const Callback & cb) : callback_(cb) {}

  virtual void call(
    const M0Event & e0, const M1Event & e1, const M2Event & e2, const M3Event & e3,
    const M4Event & e4, const M5Event & e5, const M6Event & e6, const M7Event & e7,
    const M8Event & e8)
  {
    callback_(e0, e1, e2, e3, e4, e5, e6, e7, e8);
  }

private:
  Callback callback_;
};

template <
  typename M0, typename M1, typename M2, typename M3, typename M4, typename M5, typename M6,
  typename M7, typename M8>
class Signal9
{
  using CallbackHelper9Ptr = typename CallbackHelper9<M0, M1, M2, M3, M4, M5, M6, M7, M8>::Ptr;
  using V_CallbackHelper9 = std::vector<CallbackHelper9Ptr>;

public:
  using M0Event = ipc_shared_ptr<const M0>;
  using M1Event = ipc_shared_ptr<const M1>;
  using M2Event = ipc_shared_ptr<const M2>;
  using M3Event = ipc_shared_ptr<const M3>;
  using M4Event = ipc_shared_ptr<const M4>;
  using M5Event = ipc_shared_ptr<const M5>;
  using M6Event = ipc_shared_ptr<const M6>;
  using M7Event = ipc_shared_ptr<const M7>;
  using M8Event = ipc_shared_ptr<const M8>;
  using M0ConstPtr = ipc_shared_ptr<const M0>;
  using M1ConstPtr = ipc_shared_ptr<const M1>;
  using M2ConstPtr = ipc_shared_ptr<const M2>;
  using M3ConstPtr = ipc_shared_ptr<const M3>;
  using M4ConstPtr = ipc_shared_ptr<const M4>;
  using M5ConstPtr = ipc_shared_ptr<const M5>;
  using M6ConstPtr = ipc_shared_ptr<const M6>;
  using M7ConstPtr = ipc_shared_ptr<const M7>;
  using M8ConstPtr = ipc_shared_ptr<const M8>;
  using NullP = const ipc_shared_ptr<const NullType> &;

  template <
    typename P0, typename P1, typename P2, typename P3, typename P4, typename P5, typename P6,
    typename P7, typename P8>
  Connection addCallback(const std::function<void(P0, P1, P2, P3, P4, P5, P6, P7, P8)> & callback)
  {
    CallbackHelper9T<P0, P1, P2, P3, P4, P5, P6, P7, P8, M0, M1, M2, M3, M4, M5, M6, M7, M8> *
      helper =
        new CallbackHelper9T<P0, P1, P2, P3, P4, P5, P6, P7, P8, M0, M1, M2, M3, M4, M5, M6, M7, M8>(
          callback);

    std::lock_guard<std::mutex> lock(mutex_);
    callbacks_.push_back(CallbackHelper9Ptr(helper));
    return Connection(std::bind(&Signal9::removeCallback, this, callbacks_.back()));
  }

  template <typename P0, typename P1>
  Connection addCallback(void (*callback)(P0, P1))
  {
    return addCallback(
      std::function<void(P0, P1, NullP, NullP, NullP, NullP, NullP, NullP, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2)));
  }

  template <typename P0, typename P1, typename P2>
  Connection addCallback(void (*callback)(P0, P1, P2))
  {
    return addCallback(
      std::function<void(P0, P1, P2, NullP, NullP, NullP, NullP, NullP, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3)));
  }

  template <typename P0, typename P1, typename P2, typename P3>
  Connection addCallback(void (*callback)(P0, P1, P2, P3))
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, NullP, NullP, NullP, NullP, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4)));
  }

  template <typename P0, typename P1, typename P2, typename P3, typename P4>
  Connection addCallback(void (*callback)(P0, P1, P2, P3, P4))
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, NullP, NullP, NullP, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5)));
  }

  template <typename P0, typename P1, typename P2, typename P3, typename P4, typename P5>
  Connection addCallback(void (*callback)(P0, P1, P2, P3, P4, P5))
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, NullP, NullP, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6)));
  }

  template <
    typename P0, typename P1, typename P2, typename P3, typename P4, typename P5, typename P6>
  Connection addCallback(void (*callback)(P0, P1, P2, P3, P4, P5, P6))
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, P6, NullP, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6,
        std::placeholders::_7)));
  }

  template <
    typename P0, typename P1, typename P2, typename P3, typename P4, typename P5, typename P6,
    typename P7>
  Connection addCallback(void (*callback)(P0, P1, P2, P3, P4, P5, P6, P7))
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, P6, P7, NullP)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6, std::placeholders::_7,
        std::placeholders::_8)));
  }

  template <
    typename P0, typename P1, typename P2, typename P3, typename P4, typename P5, typename P6,
    typename P7, typename P8>
  Connection addCallback(void (*callback)(P0, P1, P2, P3, P4, P5, P6, P7, P8))
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, P6, P7, P8)>(std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6, std::placeholders::_7,
        std::placeholders::_8, std::placeholders::_9)));
  }

  template <typename T, typename P0, typename P1>
  Connection addCallback(void (T::*callback)(P0, P1), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, NullP, NullP, NullP, NullP, NullP, NullP, NullP)>(
        std::bind(callback, t, std::placeholders::_1, std::placeholders::_2)));
  }

  template <typename T, typename P0, typename P1, typename P2>
  Connection addCallback(void (T::*callback)(P0, P1, P2), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, P2, NullP, NullP, NullP, NullP, NullP, NullP)>(
        std::bind(callback, t, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3)));
  }

  template <typename T, typename P0, typename P1, typename P2, typename P3>
  Connection addCallback(void (T::*callback)(P0, P1, P2, P3), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, NullP, NullP, NullP, NullP, NullP)>(std::bind(
        callback, t, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4)));
  }

  template <typename T, typename P0, typename P1, typename P2, typename P3, typename P4>
  Connection addCallback(void (T::*callback)(P0, P1, P2, P3, P4), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, NullP, NullP, NullP, NullP)>(std::bind(
        callback, t, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5)));
  }

  template <
    typename T, typename P0, typename P1, typename P2, typename P3, typename P4, typename P5>
  Connection addCallback(void (T::*callback)(P0, P1, P2, P3, P4, P5), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, NullP, NullP, NullP)>(std::bind(
        callback, t, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6)));
  }

  template <
    typename T, typename P0, typename P1, typename P2, typename P3, typename P4, typename P5,
    typename P6>
  Connection addCallback(void (T::*callback)(P0, P1, P2, P3, P4, P5, P6), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, P6, NullP, NullP)>(std::bind(
        callback, t, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6,
        std::placeholders::_7)));
  }

  template <
    typename T, typename P0, typename P1, typename P2, typename P3, typename P4, typename P5,
    typename P6, typename P7>
  Connection addCallback(void (T::*callback)(P0, P1, P2, P3, P4, P5, P6, P7), T * t)
  {
    return addCallback(
      std::function<void(P0, P1, P2, P3, P4, P5, P6, P7, NullP)>(std::bind(
        callback, t, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6, std::placeholders::_7,
        std::placeholders::_8)));
  }

  template <typename C>
  Connection addCallback(C & callback)
  {
    return addCallback<
      const M0ConstPtr &, const M1ConstPtr &, const M2ConstPtr &, const M3ConstPtr &,
      const M4ConstPtr &, const M5ConstPtr &, const M6ConstPtr &, const M7ConstPtr &,
      const M8ConstPtr &>(
      std::bind(
        callback, std::placeholders::_1, std::placeholders::_2, std::placeholders::_3,
        std::placeholders::_4, std::placeholders::_5, std::placeholders::_6, std::placeholders::_7,
        std::placeholders::_8, std::placeholders::_9));
  }

  void removeCallback(const CallbackHelper9Ptr & helper)
  {
    std::lock_guard<std::mutex> lock(mutex_);
    typename V_CallbackHelper9::iterator it =
      std::find(callbacks_.begin(), callbacks_.end(), helper);
    if (it != callbacks_.end()) {
      callbacks_.erase(it);
    }
  }

  void call(
    const M0Event & e0, const M1Event & e1, const M2Event & e2, const M3Event & e3,
    const M4Event & e4, const M5Event & e5, const M6Event & e6, const M7Event & e7,
    const M8Event & e8)
  {
    std::lock_guard<std::mutex> lock(mutex_);
    typename V_CallbackHelper9::iterator it = callbacks_.begin();
    typename V_CallbackHelper9::iterator end = callbacks_.end();
    for (; it != end; ++it) {
      const CallbackHelper9Ptr & helper = *it;
      helper->call(e0, e1, e2, e3, e4, e5, e6, e7, e8);
    }
  }

private:
  std::mutex mutex_;
  V_CallbackHelper9 callbacks_;
};

}  // namespace message_filters
}  // namespace agnocast

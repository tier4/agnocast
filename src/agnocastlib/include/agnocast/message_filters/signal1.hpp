// Copyright 2025 The Autoware Contributors
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "agnocast/agnocast_smart_pointer.hpp"

#include <functional>
#include <memory>
#include <mutex>
#include <vector>

namespace agnocast
{
namespace message_filters
{

template <class M>
class CallbackHelper1
{
public:
  virtual ~CallbackHelper1() {}

  virtual void call(const ipc_shared_ptr<const M> & msg) = 0;

  using Ptr = std::shared_ptr<CallbackHelper1<M>>;
};

template <typename P, typename M>
class CallbackHelper1T : public CallbackHelper1<M>
{
public:
  using Callback = std::function<void(P)>;

  CallbackHelper1T(const Callback & cb) : callback_(cb) {}

  virtual void call(const ipc_shared_ptr<const M> & msg) { callback_(msg); }

private:
  Callback callback_;
};

template <class M>
class Signal1
{
  using CallbackHelper1Ptr = typename CallbackHelper1<M>::Ptr;
  using V_CallbackHelper1 = std::vector<CallbackHelper1Ptr>;

public:
  template <typename P>
  CallbackHelper1Ptr addCallback(const std::function<void(P)> & callback)
  {
    CallbackHelper1T<P, M> * helper = new CallbackHelper1T<P, M>(callback);

    std::lock_guard<std::mutex> lock(mutex_);
    callbacks_.push_back(CallbackHelper1Ptr(helper));
    return callbacks_.back();
  }

  void removeCallback(const CallbackHelper1Ptr & helper)
  {
    std::lock_guard<std::mutex> lock(mutex_);
    typename V_CallbackHelper1::iterator it =
      std::find(callbacks_.begin(), callbacks_.end(), helper);
    if (it != callbacks_.end()) {
      callbacks_.erase(it);
    }
  }

  void call(const ipc_shared_ptr<const M> & msg)
  {
    std::lock_guard<std::mutex> lock(mutex_);
    typename V_CallbackHelper1::iterator it = callbacks_.begin();
    typename V_CallbackHelper1::iterator end = callbacks_.end();
    for (; it != end; ++it) {
      const CallbackHelper1Ptr & helper = *it;
      helper->call(msg);
    }
  }

private:
  std::mutex mutex_;
  V_CallbackHelper1 callbacks_;
};

}  // namespace message_filters
}  // namespace agnocast

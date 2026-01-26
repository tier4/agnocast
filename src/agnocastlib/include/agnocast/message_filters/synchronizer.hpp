#pragma once

#include "agnocast/agnocast_smart_pointer.hpp"
#include "agnocast/message_filters/signal9.hpp"

#include <rclcpp/rclcpp.hpp>

#include <message_filters/connection.h>
#include <message_filters/null_types.h>
#include <message_filters/synchronizer.h>

#include <functional>
#include <memory>
#include <string>
#include <tuple>

namespace agnocast
{
namespace message_filters
{

using ::message_filters::Connection;
using ::message_filters::noncopyable;
using ::message_filters::NullFilter;
using ::message_filters::NullType;

template <typename Policy>
class Synchronizer : public noncopyable, public Policy
{
public:
  using Messages = typename Policy::Messages;
  using Events = typename Policy::Events;
  using Signal = typename Policy::Signal;

  using M0 = typename std::tuple_element<0, Messages>::type;
  using M1 = typename std::tuple_element<1, Messages>::type;
  using M2 = typename std::tuple_element<2, Messages>::type;
  using M3 = typename std::tuple_element<3, Messages>::type;
  using M4 = typename std::tuple_element<4, Messages>::type;
  using M5 = typename std::tuple_element<5, Messages>::type;
  using M6 = typename std::tuple_element<6, Messages>::type;
  using M7 = typename std::tuple_element<7, Messages>::type;
  using M8 = typename std::tuple_element<8, Messages>::type;

  using M0Event = typename std::tuple_element<0, Events>::type;
  using M1Event = typename std::tuple_element<1, Events>::type;
  using M2Event = typename std::tuple_element<2, Events>::type;
  using M3Event = typename std::tuple_element<3, Events>::type;
  using M4Event = typename std::tuple_element<4, Events>::type;
  using M5Event = typename std::tuple_element<5, Events>::type;
  using M6Event = typename std::tuple_element<6, Events>::type;
  using M7Event = typename std::tuple_element<7, Events>::type;
  using M8Event = typename std::tuple_element<8, Events>::type;

  static const uint8_t MAX_MESSAGES = 9;

  template <typename F0, typename F1>
  Synchronizer(F0 & f0, F1 & f1)
  {
    connectInput(f0, f1);
    init();
  }

  template <typename F0, typename F1, typename F2>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2)
  {
    connectInput(f0, f1, f2);
    init();
  }

  template <typename F0, typename F1, typename F2, typename F3>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2, F3 & f3)
  {
    connectInput(f0, f1, f2, f3);
    init();
  }

  template <typename F0, typename F1, typename F2, typename F3, typename F4>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4)
  {
    connectInput(f0, f1, f2, f3, f4);
    init();
  }

  template <typename F0, typename F1, typename F2, typename F3, typename F4, typename F5>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5)
  {
    connectInput(f0, f1, f2, f3, f4, f5);
    init();
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6)
  {
    connectInput(f0, f1, f2, f3, f4, f5, f6);
    init();
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6,
    typename F7>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6, F7 & f7)
  {
    connectInput(f0, f1, f2, f3, f4, f5, f6, f7);
    init();
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6,
    typename F7, typename F8>
  Synchronizer(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6, F7 & f7, F8 & f8)
  {
    connectInput(f0, f1, f2, f3, f4, f5, f6, f7, f8);
    init();
  }

  Synchronizer() { init(); }

  template <typename F0, typename F1>
  Synchronizer(const Policy & policy, F0 & f0, F1 & f1) : Policy(policy)
  {
    connectInput(f0, f1);
    init();
  }

  template <typename F0, typename F1, typename F2>
  Synchronizer(const Policy & policy, F0 & f0, F1 & f1, F2 & f2) : Policy(policy)
  {
    connectInput(f0, f1, f2);
    init();
  }

  template <typename F0, typename F1, typename F2, typename F3>
  Synchronizer(const Policy & policy, F0 & f0, F1 & f1, F2 & f2, F3 & f3) : Policy(policy)
  {
    connectInput(f0, f1, f2, f3);
    init();
  }

  template <typename F0, typename F1, typename F2, typename F3, typename F4>
  Synchronizer(const Policy & policy, F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4) : Policy(policy)
  {
    connectInput(f0, f1, f2, f3, f4);
    init();
  }

  template <typename F0, typename F1, typename F2, typename F3, typename F4, typename F5>
  Synchronizer(const Policy & policy, F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5)
  : Policy(policy)
  {
    connectInput(f0, f1, f2, f3, f4, f5);
    init();
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6>
  Synchronizer(const Policy & policy, F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6)
  : Policy(policy)
  {
    connectInput(f0, f1, f2, f3, f4, f5, f6);
    init();
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6,
    typename F7>
  Synchronizer(
    const Policy & policy, F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6, F7 & f7)
  : Policy(policy)
  {
    connectInput(f0, f1, f2, f3, f4, f5, f6, f7);
    init();
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6,
    typename F7, typename F8>
  Synchronizer(
    const Policy & policy, F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6, F7 & f7,
    F8 & f8)
  : Policy(policy)
  {
    connectInput(f0, f1, f2, f3, f4, f5, f6, f7, f8);
    init();
  }

  explicit Synchronizer(const Policy & policy) : Policy(policy) { init(); }

  ~Synchronizer() { disconnectAll(); }

  void init() { this->initParent(this); }

  template <typename F0, typename F1>
  void connectInput(F0 & f0, F1 & f1)
  {
    NullFilter<M2> f2;
    connectInput(f0, f1, f2);
  }

  template <typename F0, typename F1, typename F2>
  void connectInput(F0 & f0, F1 & f1, F2 & f2)
  {
    NullFilter<M3> f3;
    connectInput(f0, f1, f2, f3);
  }

  template <typename F0, typename F1, typename F2, typename F3>
  void connectInput(F0 & f0, F1 & f1, F2 & f2, F3 & f3)
  {
    NullFilter<M4> f4;
    connectInput(f0, f1, f2, f3, f4);
  }

  template <typename F0, typename F1, typename F2, typename F3, typename F4>
  void connectInput(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4)
  {
    NullFilter<M5> f5;
    connectInput(f0, f1, f2, f3, f4, f5);
  }

  template <typename F0, typename F1, typename F2, typename F3, typename F4, typename F5>
  void connectInput(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5)
  {
    NullFilter<M6> f6;
    connectInput(f0, f1, f2, f3, f4, f5, f6);
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6>
  void connectInput(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6)
  {
    NullFilter<M7> f7;
    connectInput(f0, f1, f2, f3, f4, f5, f6, f7);
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6,
    typename F7>
  void connectInput(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6, F7 & f7)
  {
    NullFilter<M8> f8;
    connectInput(f0, f1, f2, f3, f4, f5, f6, f7, f8);
  }

  template <
    typename F0, typename F1, typename F2, typename F3, typename F4, typename F5, typename F6,
    typename F7, typename F8>
  void connectInput(F0 & f0, F1 & f1, F2 & f2, F3 & f3, F4 & f4, F5 & f5, F6 & f6, F7 & f7, F8 & f8)
  {
    disconnectAll();

    input_connections_[0] = f0.registerCallback([this](const M0Event & msg) { cb<0>(msg); });
    input_connections_[1] = f1.registerCallback([this](const M1Event & msg) { cb<1>(msg); });
    input_connections_[2] = f2.registerCallback([this](const M2Event & msg) { cb<2>(msg); });
    input_connections_[3] = f3.registerCallback([this](const M3Event & msg) { cb<3>(msg); });
    input_connections_[4] = f4.registerCallback([this](const M4Event & msg) { cb<4>(msg); });
    input_connections_[5] = f5.registerCallback([this](const M5Event & msg) { cb<5>(msg); });
    input_connections_[6] = f6.registerCallback([this](const M6Event & msg) { cb<6>(msg); });
    input_connections_[7] = f7.registerCallback([this](const M7Event & msg) { cb<7>(msg); });
    input_connections_[8] = f8.registerCallback([this](const M8Event & msg) { cb<8>(msg); });
  }

  template <typename C>
  Connection registerCallback(C & callback)
  {
    return signal_.addCallback(callback);
  }

  template <typename C>
  Connection registerCallback(const C & callback)
  {
    return signal_.addCallback(callback);
  }

  template <typename C, typename T>
  Connection registerCallback(C & callback, T * t)
  {
    return signal_.addCallback(callback, t);
  }

  template <typename C, typename T>
  Connection registerCallback(const C & callback, T * t)
  {
    return signal_.addCallback(callback, t);
  }

  void setName(const std::string & name) { name_ = name; }
  const std::string & getName() const { return name_; }

  void signal(
    const M0Event & e0, const M1Event & e1, const M2Event & e2, const M3Event & e3,
    const M4Event & e4, const M5Event & e5, const M6Event & e6, const M7Event & e7,
    const M8Event & e8)
  {
    signal_.call(e0, e1, e2, e3, e4, e5, e6, e7, e8);
  }

  Policy * getPolicy() { return this; }

  template <int i>
  void add(const ipc_shared_ptr<typename std::tuple_element<i, Messages>::type const> & msg)
  {
    Policy::template add<i>(typename std::tuple_element<i, Events>::type(msg));
  }

private:
  void disconnectAll()
  {
    for (auto & conn : input_connections_) {
      conn.disconnect();
    }
  }

  template <int i>
  void cb(const typename std::tuple_element<i, Events>::type & evt)
  {
    this->template add<i>(evt);
  }

  Signal signal_;
  Connection input_connections_[MAX_MESSAGES];
  std::string name_;
};

template <
  typename M0, typename M1, typename M2, typename M3, typename M4, typename M5, typename M6,
  typename M7, typename M8>
struct PolicyBase
{
  using RealTypeCount = typename ::message_filters::mp_count<
    std::tuple<M0, M1, M2, M3, M4, M5, M6, M7, M8>, NullType>::type;
  using Messages = std::tuple<M0, M1, M2, M3, M4, M5, M6, M7, M8>;
  using Signal = Signal9<M0, M1, M2, M3, M4, M5, M6, M7, M8>;
  using Events =
    std::tuple<M0Event, M1Event, M2Event, M3Event, M4Event, M5Event, M6Event, M7Event, M8Event>;

  using M0Event = ipc_shared_ptr<const M0>;
  using M1Event = ipc_shared_ptr<const M1>;
  using M2Event = ipc_shared_ptr<const M2>;
  using M3Event = ipc_shared_ptr<const M3>;
  using M4Event = ipc_shared_ptr<const M4>;
  using M5Event = ipc_shared_ptr<const M5>;
  using M6Event = ipc_shared_ptr<const M6>;
  using M7Event = ipc_shared_ptr<const M7>;
  using M8Event = ipc_shared_ptr<const M8>;
};

}  // namespace message_filters
}  // namespace agnocast

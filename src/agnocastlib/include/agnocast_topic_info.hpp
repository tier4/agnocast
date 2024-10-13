#pragma once

#include "agnocast_smart_pointer.hpp"
#include "rclcpp/rclcpp.hpp"

#include <functional>
#include <memory>

namespace agnocast
{

// Base class for a type-erased object
class AnyObject
{
public:
  virtual ~AnyObject() = default;
  virtual const std::type_info & type() const = 0;
};

// Class for a specific message types
template <typename T>
class TypedMessagePtr : public AnyObject
{
  agnocast::message_ptr<T> ptr_;

public:
  explicit TypedMessagePtr(agnocast::message_ptr<T> p) : ptr_(std::move(p)) {}

  const std::type_info & type() const override { return typeid(T); }

  // For const objects
  const agnocast::message_ptr<T> & get() const { return ptr_; }

  // For non-const objects
  agnocast::message_ptr<T> & get() { return ptr_; }
};

// Type for type-erased callback function
using TypeErasedCallback = std::function<void(const AnyObject &)>;

// Primary template
template <typename T>
struct function_traits;

// Extract the args type of a not-const method
template <typename ClassType, typename ReturnType, typename... Args>
struct function_traits<ReturnType (ClassType::*)(Args...)>
{
  static constexpr std::size_t arity = sizeof...(Args);

  template <std::size_t Index>
  using arg = typename std::tuple_element<Index, std::tuple<Args...>>::type;
};

// Extract the args type of a const method
template <typename ClassType, typename ReturnType, typename... Args>
struct function_traits<ReturnType (ClassType::*)(Args...) const>
{
  static constexpr std::size_t arity = sizeof...(Args);

  template <std::size_t Index>
  using arg = typename std::tuple_element<Index, std::tuple<Args...>>::type;
};

// Specialization for std::function
template <typename ReturnType, typename... Args>
struct function_traits<std::function<ReturnType(Args...)>>
{
  static constexpr std::size_t arity = sizeof...(Args);

  template <std::size_t Index>
  using arg = typename std::tuple_element<Index, std::tuple<Args...>>::type;
};

// Extract the first arg type of a method
template <typename Func>
struct callback_first_arg
{
  using type = typename std::decay<typename function_traits<Func>::template arg<0>>::type;
};

// Specialization for std::function
template <typename ReturnType, typename Arg, typename... Args>
struct callback_first_arg<std::function<ReturnType(Arg, Args...)>>
{
  using type = typename std::decay<Arg>::type;
};

struct AgnocastTopicInfo
{
  uint32_t topic_local_id;
  const char * topic_name;
  uint32_t qos_depth;
  mqd_t mqdes;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  TypeErasedCallback callback;
  std::function<std::unique_ptr<AnyObject>(void *, const char *, uint32_t, uint64_t, bool)>
    message_creator;
  bool need_epoll_update;
};

extern std::unordered_map<uint32_t, AgnocastTopicInfo> id2_topic_mq_info;
extern std::atomic<int> agnocast_topic_next_id;
extern std::atomic<bool> need_epoll_updates;

template <typename Func>
static void register_callback(
  Func method, const char * topic_name, uint32_t qos_depth, mqd_t mqdes,
  rclcpp::CallbackGroup::SharedPtr callback_group)
{
  using MessagePtrType = typename callback_first_arg<Func>::type;
  using MessageType = typename MessagePtrType::element_type;

  auto erased_func = [method](const AnyObject & arg) {
    if (typeid(MessageType) == arg.type()) {
      const auto & typed_arg = static_cast<const TypedMessagePtr<MessageType> &>(arg);
      method(typed_arg.get());
    } else {
      throw std::bad_cast();
    }
  };

  auto message_creator = [](
                           void * ptr, const char * topic_name, uint32_t publisher_pid,
                           uint64_t timestamp, bool need_rc_update) {
    return std::make_unique<TypedMessagePtr<MessageType>>(agnocast::message_ptr<MessageType>(
      static_cast<MessageType *>(ptr), topic_name, publisher_pid, timestamp, need_rc_update));
  };

  int id = agnocast_topic_next_id.fetch_add(1);
  id2_topic_mq_info[id] = AgnocastTopicInfo{
    id, topic_name, qos_depth, mqdes, callback_group, erased_func, message_creator, true};
  need_epoll_updates.store(true);
}

static std::function<void()> create_callable(
  void * ptr, const char * topic_name, uint32_t publisher_pid, uint64_t timestamp,
  bool need_rc_update, int topic_local_id)
{
  auto it = id2_topic_mq_info.find(topic_local_id);
  if (it == id2_topic_mq_info.end()) {
    throw std::runtime_error("callback not found");
  }

  const auto & info = it->second;
  return [ptr, topic_name, publisher_pid, timestamp, need_rc_update, &info]() {
    auto typed_msg =
      info.message_creator(ptr, topic_name, publisher_pid, timestamp, need_rc_update);
    info.callback(*typed_msg);
  };
}

}  // namespace agnocast

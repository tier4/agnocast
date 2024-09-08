#pragma once

#include "agnocast_smart_pointer.hpp"

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
  int topic_local_id;
  mqd_t mqdes;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  TypeErasedCallback callback;
};

extern std::unordered_map<size_t, AgnocastTopicInfo> id2_topic_mq_info;
extern std::atomic<int> agnocast_topic_id;

template <typename Func>
int register_callback(Func method, mqd_t mqdes, rclcpp::CallbackGroup::SharedPtr callback_group)
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

  int id = agnocast_topic_id.fetch_add(1);
  id2_topic_mq_info[id] = AgnocastTopicInfo{id, mqdes, callback_group, erased_func};

  return id;
}

template <typename T>
std::function<void()> create_callable(const agnocast::message_ptr<T> & msg, int topic_local_id)
{
  auto it = id2_topic_mq_info.find(topic_local_id);
  if (it == id2_topic_mq_info.end()) {
    throw std::runtime_error("callback not found");
  }

  const auto & callback = it->second.callback;
  return [msg, callback]() {
    TypedMessagePtr<T> typed_msg(msg);
    callback(typed_msg);
  };
}

}  // namespace agnocast

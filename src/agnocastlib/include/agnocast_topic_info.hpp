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
  agnocast::ipc_shared_ptr<T> ptr_;

public:
  explicit TypedMessagePtr(agnocast::ipc_shared_ptr<T> p) : ptr_(std::move(p)) {}

  const std::type_info & type() const override { return typeid(T); }

  // For const objects
  const agnocast::ipc_shared_ptr<T> & get() const { return ptr_; }

  // For non-const objects
  agnocast::ipc_shared_ptr<T> & get() { return ptr_; }
};

// Type for type-erased callback function
using TypeErasedCallback = std::function<void(const AnyObject &)>;

// Primary template
template <typename T>
struct function_traits;

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
  std::string topic_name;
  uint32_t qos_depth;                               // used later to implement executors
  mqd_t mqdes;                                      // used later to implement executors
  rclcpp::CallbackGroup::SharedPtr callback_group;  // used later to implement executors
  TypeErasedCallback callback;
  std::function<std::unique_ptr<AnyObject>(void *, const std::string &, uint32_t, uint64_t, bool)>
    message_creator;
};

extern std::unordered_map<uint32_t, AgnocastTopicInfo> id2_topic_mq_info;
extern std::atomic<uint32_t> agnocast_topic_next_id;

template <typename Func>
uint32_t register_callback(
  Func method, const std::string & topic_name, uint32_t qos_depth, mqd_t mqdes,
  rclcpp::CallbackGroup::SharedPtr callback_group)
{
  using MessagePtrType = typename callback_first_arg<Func>::type;
  using MessageType = typename MessagePtrType::element_type;

  auto erased_func = [method](const AnyObject & arg) {
    if (typeid(MessageType) == arg.type()) {
      const auto & typed_arg = static_cast<const TypedMessagePtr<MessageType> &>(arg);
      method(typed_arg.get());
    } else {
      RCLCPP_ERROR(logger, "bad allocation in register_callback");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  };

  auto message_creator = [](
                           void * ptr, const std::string & topic_name, uint32_t publisher_pid,
                           uint64_t timestamp, bool need_rc_update) {
    return std::make_unique<TypedMessagePtr<MessageType>>(agnocast::ipc_shared_ptr<MessageType>(
      static_cast<MessageType *>(ptr), topic_name, publisher_pid, timestamp, need_rc_update));
  };

  uint32_t id = agnocast_topic_next_id.fetch_add(1);
  id2_topic_mq_info[id] =
    AgnocastTopicInfo{topic_name, qos_depth, mqdes, callback_group, erased_func, message_creator};
  return id;
}

static std::function<void()> create_callable(
  void * ptr, uint32_t publisher_pid, uint64_t timestamp, uint32_t topic_local_id)
{
  auto it = id2_topic_mq_info.find(topic_local_id);
  if (it == id2_topic_mq_info.end()) {
    RCLCPP_ERROR(logger, "callback is not registered with topic_local_id=%d", topic_local_id);
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  const auto & info = it->second;
  return [ptr, publisher_pid, timestamp, &info]() {
    auto typed_msg = info.message_creator(ptr, info.topic_name, publisher_pid, timestamp, true);
    info.callback(*typed_msg);
  };
}

}  // namespace agnocast

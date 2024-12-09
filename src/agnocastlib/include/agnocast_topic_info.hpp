#pragma once

#include "agnocast_smart_pointer.hpp"

#include <mutex>

namespace agnocast
{

// Base class for a type-erased object
class AnyObject
{
public:
  virtual ~AnyObject() = default;
  virtual const std::type_info & type() const = 0;
};

// Class for a specific message type
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
  uint32_t qos_depth;
  mqd_t mqdes;
  rclcpp::CallbackGroup::SharedPtr callback_group;
  TypeErasedCallback callback;
  std::function<std::unique_ptr<AnyObject>(
    const void *, const std::string &, const uint32_t, const uint64_t, const bool)>
    message_creator;
  bool need_epoll_update = true;
};

extern std::mutex id2_topic_mq_info_mtx;
extern std::unordered_map<uint32_t, AgnocastTopicInfo> id2_topic_mq_info;
extern std::atomic<uint32_t> agnocast_topic_next_id;
extern std::atomic<bool> need_epoll_updates;

template <typename T, typename Func>
TypeErasedCallback get_erased_callback(const Func callback)
{
  return [callback](const AnyObject & arg) {
    if (typeid(T) == arg.type()) {
      const auto & typed_arg = static_cast<const TypedMessagePtr<T> &>(arg);
      callback(typed_arg.get());
    } else {
      RCLCPP_ERROR(
        logger, "Agnocast internal implementation error: bad allocation when callback is called");
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  };
}

template <typename Func>
void register_callback(
  const Func callback, const std::string & topic_name, const uint32_t qos_depth, const mqd_t mqdes,
  const rclcpp::CallbackGroup::SharedPtr callback_group)
{
  using MessagePtrType = typename callback_first_arg<Func>::type;
  using MessageType = typename MessagePtrType::element_type;

  TypeErasedCallback erased_callback = get_erased_callback<MessageType>(callback);

  auto message_creator = [](
                           const void * ptr, const std::string & topic_name,
                           const uint32_t publisher_pid, const uint64_t timestamp,
                           const bool is_created_by_sub) {
    return std::make_unique<TypedMessagePtr<MessageType>>(agnocast::ipc_shared_ptr<MessageType>(
      const_cast<MessageType *>(static_cast<const MessageType *>(ptr)), topic_name, publisher_pid,
      timestamp, is_created_by_sub));
  };

  uint32_t id = agnocast_topic_next_id.fetch_add(1);

  {
    std::lock_guard<std::mutex> lock(id2_topic_mq_info_mtx);
    id2_topic_mq_info[id] = AgnocastTopicInfo{topic_name,     qos_depth,       mqdes,
                                              callback_group, erased_callback, message_creator};
  }

  need_epoll_updates.store(true);
}

std::shared_ptr<std::function<void()>> create_callable(
  const void * ptr, const uint32_t publisher_pid, const uint64_t timestamp,
  const uint32_t topic_local_id);

}  // namespace agnocast

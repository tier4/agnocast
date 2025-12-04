#include "agnocast/agnocast_context.hpp"
#include "agnocast/agnocast_publisher.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "agnocast/agnocast_timer_info.hpp"

#include <algorithm>
#include <chrono>
#include <memory>
#include <string>

namespace agnocast
{

inline std::string query_node_name()
{
  std::string node_name;
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    node_name = g_context.command_line_params.node_name;
  }
  return node_name;
}

class Node
{
  std::string node_name_;
  rclcpp::Logger logger_;
  rclcpp::CallbackGroup::SharedPtr default_callback_group_;

public:
  using SharedPtr = std::shared_ptr<Node>;

  Node() : node_name_(query_node_name()), logger_(rclcpp::get_logger(node_name_))
  {
    default_callback_group_ =
      std::make_shared<rclcpp::CallbackGroup>(rclcpp::CallbackGroupType::MutuallyExclusive);
  }

  rclcpp::Logger get_logger() const { return logger_; }

  std::string get_name() const { return node_name_; }

  // TODO(sykwer): Implement get_fully_qualified_name with valid logic, similar to rclcpp::Node.
  const char * get_fully_qualified_name() const { return node_name_.c_str(); }

  rclcpp::CallbackGroup::SharedPtr get_default_callback_group() const
  {
    return default_callback_group_;
  }

  // cppcheck-suppress functionStatic
  bool callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & callback_group) const
  {
    (void)callback_group;
    // TODO(sykwer): implement proper logic after create_callback_group() method is implemented.
    return true;
  }

  template <typename MessageT, typename Func>
  typename agnocast::Subscription<MessageT>::SharedPtr create_subscription(
    const std::string & topic_name, size_t queue_size, Func && callback,
    agnocast::SubscriptionOptions options)
  {
    return std::make_shared<Subscription<MessageT>>(
      this, topic_name, rclcpp::QoS(rclcpp::KeepLast(queue_size)), std::forward<Func>(callback),
      options);
  }

  template <typename MessageT>
  typename agnocast::Publisher<MessageT>::SharedPtr create_publisher(
    const std::string & topic_name, size_t queue_size)
  {
    return std::make_shared<Publisher<MessageT>>(
      this, topic_name, rclcpp::QoS(rclcpp::KeepLast(queue_size)));
  }

  template <typename Func>
  uint32_t create_wall_timer(
    std::chrono::nanoseconds period, Func && callback,
    rclcpp::CallbackGroup::SharedPtr group = nullptr)
  {
    if (!group) {
      group = default_callback_group_;
    }

    // Check if callback accepts TimerCallbackInfo&
    if constexpr (std::is_invocable_v<Func, TimerCallbackInfo &>) {
      return register_timer(std::forward<Func>(callback), period, group);
    } else {
      // Wrap void() callback to match TimerCallbackInfo& signature
      static_assert(
        std::is_invocable_v<Func>,
        "Callback must be callable with void() or void(TimerCallbackInfo&)");
      auto wrapped = [cb = std::forward<Func>(callback)](TimerCallbackInfo &) { cb(); };
      return register_timer(std::move(wrapped), period, group);
    }
  }
};

}  // namespace agnocast

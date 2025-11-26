#include "agnocast/agnocast_context.hpp"
#include "agnocast/agnocast_subscription.hpp"

#include <memory>

namespace agnocast
{

extern Context g_context;
extern std::mutex g_context_mtx;

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

  // TODO: Implement get_fully_qualified_name with valid logic, similar to rclcpp::Node.
  const char * get_fully_qualified_name() const { return node_name_.c_str(); }

  rclcpp::CallbackGroup::SharedPtr get_default_callback_group() const
  {
    return default_callback_group_;
  }

  bool callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & callback_group) const
  {
    (void)callback_group;
    // TODO: implement proper logic after create_callback_group() method is implemented.
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
};

}  // namespace agnocast

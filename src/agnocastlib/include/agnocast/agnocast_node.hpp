#pragma once

#include "agnocast/agnocast_context.hpp"
#include "agnocast/tmp_agnocast_subscription.hpp"
#include "rclcpp/rclcpp.hpp"

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

public:
  using SharedPtr = std::shared_ptr<Node>;

  Node() : node_name_(query_node_name()), logger_(rclcpp::get_logger(node_name_)) {}

  rclcpp::Logger get_logger() const { return logger_; }

  std::string get_name() const { return node_name_; }

  template <typename MessageT, typename Func>
  typename TmpSubscription<MessageT>::SharedPtr create_subscription(
    const std::string & topic_name, size_t queue_size, Func && callback,
    SubscriptionOptions options)
  {
    return agnocast::tmp_create_subscription<MessageT>(
      get_name(), topic_name, queue_size, std::forward<Func>(callback), options);
  }
};

}  // namespace agnocast

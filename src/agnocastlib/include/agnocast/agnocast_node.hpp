#pragma once

#include "agnocast/agnocast_context.hpp"

#include <memory>
#include <string>

#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

inline std::string query_node_name()
{
  std::string node_name;
  std::lock_guard<std::mutex> lock(g_context_mtx);
  if (g_context.is_initialized()) {
    for (const auto & rule : g_context.get_remap_rules()) {
      if (rule.type == RemapType::NODENAME) {
        node_name = rule.replacement;
        break;
      }
    }
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
};

}  // namespace agnocast

#include "rclcpp/rclcpp.hpp"

#include <memory>

namespace agnocast
{

class Node
{
  rclcpp::Logger logger_;

public:
  using SharedPtr = std::shared_ptr<Node>;

  Node() : logger_(rclcpp::get_logger("TODO: how to name this logger")) {}

  rclcpp::Logger get_logger() const { return logger_; }
};

}  // namespace agnocast

#include "agnocast/agnocast.hpp"

#include <iostream>

class NoRclcppSubscriber : public agnocast::Node
{
public:
  explicit NoRclcppSubscriber()
  {
    RCLCPP_INFO(get_logger(), "NoRclcppSubscriber node (name=%s) started.", get_name().c_str());
  }
};

int main(int argc, char ** argv)
{
  agnocast::init(argc, argv);
  auto node = std::make_shared<NoRclcppSubscriber>();
  return 0;
}

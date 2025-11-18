#include "agnocast/agnocast_mq.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

using BridgeFn = std::shared_ptr<rclcpp::Node> (*)(const BridgeArgs &);

}  // namespace agnocast

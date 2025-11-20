#include "agnocast/agnocast_bridge_main.hpp"

#include "agnocast/agnocast_bridge_process.hpp"

namespace agnocast
{

void bridge_main(const MqMsgBridge & req)
{
  rclcpp::init(0, nullptr);
  int exit_code = EXIT_SUCCESS;

  auto logger = rclcpp::get_logger("agnocast_bridge_main");

  try {
    BridgeProcess bridge(req);
    bridge.run();
  } catch (const std::exception & e) {
    RCLCPP_FATAL(logger, "Bridge process failed during initialization: %s", e.what());
    exit_code = EXIT_FAILURE;
  } catch (...) {
    RCLCPP_FATAL(logger, "Bridge process failed during initialization with unknown exception.");
    exit_code = EXIT_FAILURE;
  }

  rclcpp::shutdown();
  exit(exit_code);
}

}  // namespace agnocast

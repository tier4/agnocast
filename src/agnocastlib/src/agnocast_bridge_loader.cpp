#include "agnocast/agnocast_bridge_loader.hpp"

namespace agnocast
{

BridgeLoader::BridgeLoader(const rclcpp::Logger & logger) : logger_(logger)
{
}

BridgeLoader::~BridgeLoader()
{
  cached_factories_.clear();
}

std::shared_ptr<void> BridgeLoader::load_and_create(
  const MqMsgBridge & req, const std::string & topic_name_with_direction,
  rclcpp::Node::SharedPtr node)
{
  // TODO(yutarokobayashi): The following comments are scheduled for implementation in a later PR.

  // Resolve the factory function and library handle from the shared library using the
  // topic_name_with_direction.

  // Validate the resolution result.
  //    If the factory function pointer is invalid (null):
  //      - Retrieve the dynamic linking error message (dlerror).
  //      - Log an error message indicating the failure to resolve the factory.
  //      - Return nullptr to stop the process.

  // Invoke the resolved factory function to create the bridge instance and return it.
  return nullptr;
}

}  // namespace agnocast

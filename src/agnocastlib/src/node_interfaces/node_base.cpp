#include "agnocast/node_interfaces/node_base.hpp"
#include "agnocast/agnocast_context.hpp"

#include <algorithm>

namespace agnocast
{
namespace node_interfaces
{

NodeBase::NodeBase(
  const std::string & node_name,
  const std::string & ns)
: node_name_(node_name)
{
  // Normalize namespace (ensure it starts with '/' or is empty)
  if (!ns.empty() && ns[0] != '/') {
    namespace_ = "/" + ns;
  } else {
    namespace_ = ns;
  }

  // Apply node name and namespace remapping from GlobalContext
  // Corresponds to rcl_node_init calling rcl_remap_node_name and rcl_remap_node_namespace
  // in rcl/src/rcl/node.c:222-242
  auto & global_ctx = GlobalContext::instance();
  if (global_ctx.is_initialized()) {
    auto global_rules = global_ctx.get_remap_rules();

    for (const auto & rule : global_rules) {
      if (rule.type == RemapType::NODENAME) {
        node_name_ = rule.replacement;
      } else if (rule.type == RemapType::NAMESPACE) {
        // Apply namespace remapping
        // Corresponds to rcl_remap_node_namespace in rcl/src/rcl/remap.c
        namespace_ = rule.replacement;
        // Normalize namespace: ensure it starts with '/'
        if (!namespace_.empty() && namespace_[0] != '/') {
          namespace_ = "/" + namespace_;
        }
      }
    }
  }

  // Initialize default callback group
  default_callback_group_ =
    rclcpp::CallbackGroup::SharedPtr(new rclcpp::CallbackGroup(
      rclcpp::CallbackGroupType::MutuallyExclusive));
  callback_groups_.push_back(default_callback_group_);
}

std::string NodeBase::get_name() const
{
  return node_name_;
}

std::string NodeBase::get_namespace() const
{
  return namespace_;
}

std::string NodeBase::get_fully_qualified_name() const
{
  // Corresponds to rcl_node_get_fully_qualified_name in rcl/src/rcl/node.c:453-459
  // Returns the fully qualified node name (namespace/node_name)
  // Example: namespace="/foo", node_name="bar" -> "/foo/bar"
  // Example: namespace="/", node_name="bar" -> "/bar"
  if (namespace_.empty() || namespace_ == "/") {
    return "/" + node_name_;
  }
  return namespace_ + "/" + node_name_;
}

rclcpp::CallbackGroup::SharedPtr
NodeBase::create_callback_group(
  rclcpp::CallbackGroupType group_type,
  bool automatically_add_to_executor_with_node)
{
  // Corresponds to rclcpp::Node::create_callback_group
  // in rclcpp/src/rclcpp/node.cpp:316-323
  auto group = rclcpp::CallbackGroup::SharedPtr(new rclcpp::CallbackGroup(group_type));
  if (automatically_add_to_executor_with_node) {
    callback_groups_.push_back(group);
  }
  return group;
}

rclcpp::CallbackGroup::SharedPtr
NodeBase::get_default_callback_group()
{
  return default_callback_group_;
}

bool
NodeBase::callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & group)
{
  // Corresponds to rclcpp::Node::callback_group_in_node
  // in rclcpp/src/rclcpp/node.cpp:330-341
  auto it = std::find_if(
    callback_groups_.begin(),
    callback_groups_.end(),
    [&group](const rclcpp::CallbackGroup::WeakPtr & weak_group) {
      auto shared_group = weak_group.lock();
      return shared_group && shared_group == group;
    });
  return it != callback_groups_.end();
}

}  // namespace node_interfaces
}  // namespace agnocast

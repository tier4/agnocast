#include "agnocast/node_interfaces/node_base.hpp"

#include "agnocast/agnocast_context.hpp"
#include "rclcpp/contexts/default_context.hpp"

#include <algorithm>
#include <stdexcept>

namespace agnocast
{
namespace node_interfaces
{

NodeBase::NodeBase(const std::string & node_name, const std::string & ns)
: NodeBase(node_name, ns, rclcpp::contexts::get_global_default_context())
{
}

NodeBase::NodeBase(
  const std::string & node_name, const std::string & ns, rclcpp::Context::SharedPtr context)
: node_name_(node_name), context_(context)
{
  // Normalize namespace (ensure it starts with '/' or is empty)
  if (!ns.empty() && ns[0] != '/') {
    namespace_ = "/" + ns;
  } else {
    namespace_ = ns;
  }

  // Apply node name and namespace remapping from agnocast::Context
  // Corresponds to rcl_node_init calling rcl_remap_node_name and rcl_remap_node_namespace
  // in rcl/src/rcl/node.c:222-242
  {
    std::lock_guard<std::mutex> lock(g_context_mtx);
    auto & global_ctx = g_context;
    if (global_ctx.is_initialized()) {
      auto global_rules = global_ctx.get_remap_rules();

      for (const auto & rule : global_rules) {
        if (rule.type == RemapType::NODE_NAME) {
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
  }

  initialize_common();
}

void NodeBase::initialize_common()
{
  // Build fully qualified name
  if (namespace_.empty() || namespace_ == "/") {
    fqn_ = "/" + node_name_;
  } else {
    fqn_ = namespace_ + "/" + node_name_;
  }

  // Initialize default callback group
  default_callback_group_ =
    std::make_shared<rclcpp::CallbackGroup>(rclcpp::CallbackGroupType::MutuallyExclusive);
  callback_groups_.push_back(default_callback_group_);

  // Initialize guard condition if context is valid
  if (context_ && context_->is_valid()) {
    notify_guard_condition_ = std::make_unique<rclcpp::GuardCondition>(context_);
    notify_guard_condition_is_valid_ = true;
  }
}

const char * NodeBase::get_name() const
{
  return node_name_.c_str();
}

const char * NodeBase::get_namespace() const
{
  return namespace_.c_str();
}

const char * NodeBase::get_fully_qualified_name() const
{
  return fqn_.c_str();
}

rclcpp::Context::SharedPtr NodeBase::get_context()
{
  return context_;
}

rcl_node_t * NodeBase::get_rcl_node_handle()
{
  throw std::runtime_error(
    "rcl_node_handle is not available in agnocast::Node. "
    "This node does not use DDS.");
}

const rcl_node_t * NodeBase::get_rcl_node_handle() const
{
  throw std::runtime_error(
    "rcl_node_handle is not available in agnocast::Node. "
    "This node does not use DDS.");
}

std::shared_ptr<rcl_node_t> NodeBase::get_shared_rcl_node_handle()
{
  throw std::runtime_error(
    "rcl_node_handle is not available in agnocast::Node. "
    "This node does not use DDS.");
}

std::shared_ptr<const rcl_node_t> NodeBase::get_shared_rcl_node_handle() const
{
  throw std::runtime_error(
    "rcl_node_handle is not available in agnocast::Node. "
    "This node does not use DDS.");
}

rclcpp::CallbackGroup::SharedPtr NodeBase::create_callback_group(
  rclcpp::CallbackGroupType group_type, bool automatically_add_to_executor_with_node)
{
  (void)group_type;
  (void)automatically_add_to_executor_with_node;
  // TODO
  return nullptr;
}

rclcpp::CallbackGroup::SharedPtr NodeBase::get_default_callback_group()
{
  return default_callback_group_;
}

bool NodeBase::callback_group_in_node(rclcpp::CallbackGroup::SharedPtr group)
{
  (void)group;
  // TODO
  return false;
}

void NodeBase::for_each_callback_group(const CallbackGroupFunction & func)
{
  (void)func;
  // TODO
}

std::atomic_bool & NodeBase::get_associated_with_executor_atomic()
{
  return associated_with_executor_;
}

// NOTE: Thread safety limitation - this function returns a reference after releasing the lock.
// The caller may use the returned reference while another thread modifies notify_guard_condition_.
// This is a potential data race. However, rclcpp's implementation has the same issue:
// rclcpp/src/rclcpp/node_interfaces/node_base.cpp:246-253 also returns a reference after
// releasing the lock. The interface signature (returning a reference) is defined by
// rclcpp::node_interfaces::NodeBaseInterface, so we cannot change it without breaking
// compatibility. In practice, notify_guard_condition_ is typically not modified during
// the node's lifetime after initialization, so this is unlikely to cause issues.
rclcpp::GuardCondition & NodeBase::get_notify_guard_condition()
{
  std::lock_guard<std::recursive_mutex> lock(notify_guard_condition_mutex_);
  if (!notify_guard_condition_is_valid_ || !notify_guard_condition_) {
    throw std::runtime_error(
      "Notify guard condition is not valid. "
      "Ensure rclcpp::Context is valid (rclcpp::init() was called or "
      "valid NodeOptions.context() was provided).");
  }
  return *notify_guard_condition_;
}

bool NodeBase::get_use_intra_process_default() const
{
  // TODO
  return false;
}

bool NodeBase::get_enable_topic_statistics_default() const
{
  // TODO
  return false;
}

std::string NodeBase::resolve_topic_or_service_name(
  const std::string & name, bool is_service, bool only_expand) const
{
  (void)name;
  (void)is_service;
  (void)only_expand;
  // TODO
  return "";
}

}  // namespace node_interfaces
}  // namespace agnocast

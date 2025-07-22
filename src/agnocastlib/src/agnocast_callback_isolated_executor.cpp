#include <agnocast/agnocast.hpp>
#include <agnocast/agnocast_callback_isolated_executor.hpp>
#include <agnocast/agnocast_single_threaded_executor.hpp>
#include <rclcpp/rclcpp.hpp>

namespace agnocast
{

CallbackIsolatedAgnocastExecutor::CallbackIsolatedAgnocastExecutor(
  const rclcpp::ExecutorOptions & options)
: rclcpp::Executor(options)
{
}

void CallbackIsolatedAgnocastExecutor::spin()
{
  if (spinning.exchange(true)) {
    RCLCPP_ERROR(logger, "spin() called while already spinning");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void CallbackIsolatedAgnocastExecutor::add_callback_group(
  rclcpp::CallbackGroup::SharedPtr group_ptr,
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify)
{
  (void)group_ptr;
  (void)node_ptr;
  (void)notify;
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_all_callback_groups()
{
  return {};
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_manually_added_callback_groups()
{
  return {};
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_automatically_added_callback_groups_from_nodes()
{
  return {};
}

void CallbackIsolatedAgnocastExecutor::remove_callback_group(
  rclcpp::CallbackGroup::SharedPtr group_ptr, bool notify)
{
  (void)group_ptr;
  (void)notify;
}

void CallbackIsolatedAgnocastExecutor::add_node(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify)
{
  (void)node_ptr;
  (void)notify;
}

void CallbackIsolatedAgnocastExecutor::add_node(rclcpp::Node::SharedPtr node_ptr, bool notify)
{
  (void)node_ptr;
  (void)notify;
}

void CallbackIsolatedAgnocastExecutor::remove_node(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify)
{
  (void)node_ptr;
  (void)notify;
}

void CallbackIsolatedAgnocastExecutor::remove_node(rclcpp::Node::SharedPtr node_ptr, bool notify)
{
  (void)node_ptr;
  (void)notify;
}

}  // namespace agnocast

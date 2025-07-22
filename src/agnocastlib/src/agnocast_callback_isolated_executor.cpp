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
  (void)notify;

  std::weak_ptr<rclcpp::CallbackGroup> weak_group_ptr = group_ptr;
  std::weak_ptr<rclcpp::node_interfaces::NodeBaseInterface> weak_node_ptr = node_ptr;

  std::lock_guard<std::mutex> guard{mutex_};

  // Confirm that group_ptr does not refer to any of the callback groups held by nodes in
  // weak_nodes_.
  for (const auto & weak_node : weak_nodes_) {
    auto n = weak_node.lock();

    if (!n) {
      continue;
    }

    if (n->callback_group_in_node(group_ptr)) {
      RCLCPP_ERROR(
        logger, "Callback group already exists in node: %s", n->get_fully_qualified_name());
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  }

  auto insert_info = weak_groups_to_nodes_.insert(std::make_pair(weak_group_ptr, weak_node_ptr));

  if (!insert_info.second) {
    RCLCPP_ERROR(logger, "Callback group already exists in the executor");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_all_callback_groups()
{
  return {};
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_manually_added_callback_groups()
{
  std::lock_guard<std::mutex> guard{mutex_};
  return get_manually_added_callback_groups_internal();
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_manually_added_callback_groups_internal() const
{
  std::vector<rclcpp::CallbackGroup::WeakPtr> groups;

  for (const auto & weak_group_to_node : weak_groups_to_nodes_) {
    auto group = weak_group_to_node.first.lock();
    if (group) {
      groups.push_back(group);
    }
  }

  return groups;
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_automatically_added_callback_groups_from_nodes()
{
  return {};
}

void CallbackIsolatedAgnocastExecutor::remove_callback_group(
  rclcpp::CallbackGroup::SharedPtr group_ptr, bool notify)
{
  (void)notify;

  std::lock_guard<std::mutex> guard{mutex_};

  auto it = weak_groups_to_nodes_.find(group_ptr);

  if (it != weak_groups_to_nodes_.end()) {
    weak_groups_to_nodes_.erase(it);
  } else {
    RCLCPP_ERROR(logger, "Callback group not found in the executor");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
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

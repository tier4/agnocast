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

  RCPPUTILS_SCOPE_EXIT(this->spinning.store(false););

  std::vector<std::thread> threads;
  std::vector<std::pair<
    rclcpp::CallbackGroup::SharedPtr, rclcpp::node_interfaces::NodeBaseInterface::SharedPtr>>
    groups_and_nodes;

  {
    std::lock_guard<std::mutex> guard{mutex_};

    for (const auto & weak_group_to_node : weak_groups_to_nodes_) {
      auto group = weak_group_to_node.first.lock();
      if (!group) {
        continue;
      }

      auto node = weak_group_to_node.second.lock();
      if (!node) {
        continue;
      }

      groups_and_nodes.emplace_back(group, node);
    }

    for (const auto & weak_node : weak_nodes_) {
      auto node = weak_node.lock();
      if (!node) {
        continue;
      }

      node->for_each_callback_group(
        [&groups_and_nodes, node](const rclcpp::CallbackGroup::SharedPtr & group) {
          if (group && group->automatically_add_to_executor_with_node()) {
            groups_and_nodes.emplace_back(group, node);
          }
        });
    }
  }  // guard mutex_

  for (auto [group, node] : groups_and_nodes) {
    auto executor = std::make_shared<SingleThreadedAgnocastExecutor>();
    executor->dedicate_to_callback_group(group, node);

    threads.emplace_back([executor]() {
      auto tid = std::this_thread::get_id();
      RCLCPP_INFO(
        rclcpp::get_logger("agnocast"), "Thread ID: %zu", std::hash<std::thread::id>{}(tid));
      executor->spin();
    });
  }

  for (auto & thread : threads) {
    if (thread.joinable()) {
      thread.join();
    }
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
  std::lock_guard<std::mutex> guard{mutex_};
  std::vector<rclcpp::CallbackGroup::WeakPtr> groups;

  auto manually_added_groups = get_manually_added_callback_groups_internal();
  auto automatically_added_groups = get_automatically_added_callback_groups_from_nodes_internal();

  groups.reserve(manually_added_groups.size() + automatically_added_groups.size());
  groups.insert(groups.end(), manually_added_groups.begin(), manually_added_groups.end());
  groups.insert(groups.end(), automatically_added_groups.begin(), automatically_added_groups.end());

  return groups;
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
  std::lock_guard<std::mutex> guard{mutex_};
  return get_automatically_added_callback_groups_from_nodes_internal();
}

std::vector<rclcpp::CallbackGroup::WeakPtr>
CallbackIsolatedAgnocastExecutor::get_automatically_added_callback_groups_from_nodes_internal()
  const
{
  std::vector<rclcpp::CallbackGroup::WeakPtr> groups;

  for (const auto & weak_node : weak_nodes_) {
    auto node = weak_node.lock();

    if (!node) {
      continue;
    }

    node->for_each_callback_group([&groups](const rclcpp::CallbackGroup::SharedPtr & group) {
      if (group && group->automatically_add_to_executor_with_node()) {
        groups.push_back(group);
      }
    });
  }

  return groups;
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
  (void)notify;

  std::lock_guard<std::mutex> guard{mutex_};

  // Confirm that any callback group in weak_groups_to_nodes_ does not refer to any of the callback
  // groups held by node_ptr.
  for (const auto & weak_group_to_node : weak_groups_to_nodes_) {
    auto group = weak_group_to_node.first.lock();

    if (!group) {
      continue;
    }

    if (node_ptr->callback_group_in_node(group)) {
      RCLCPP_ERROR(
        logger, "One of the callback groups in node %s already exists in the executor.",
        node_ptr->get_fully_qualified_name());
      close(agnocast_fd);
      exit(EXIT_FAILURE);
    }
  }

  std::weak_ptr<rclcpp::node_interfaces::NodeBaseInterface> weak_node_ptr = node_ptr;

  auto insert_info = weak_nodes_.insert(weak_node_ptr);
  if (!insert_info.second) {
    RCLCPP_ERROR(
      logger, "Node already exists in the executor: %s", node_ptr->get_fully_qualified_name());
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void CallbackIsolatedAgnocastExecutor::add_node(rclcpp::Node::SharedPtr node_ptr, bool notify)
{
  (void)notify;
  add_node(node_ptr->get_node_base_interface(), notify);
}

void CallbackIsolatedAgnocastExecutor::remove_node(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify)
{
  (void)notify;

  std::weak_ptr<rclcpp::node_interfaces::NodeBaseInterface> weak_node_ptr = node_ptr;
  std::lock_guard<std::mutex> guard{mutex_};

  auto it = weak_nodes_.find(weak_node_ptr);

  if (it != weak_nodes_.end()) {
    weak_nodes_.erase(it);
  } else {
    RCLCPP_ERROR(
      logger, "Node not found in the executor: %s", node_ptr->get_fully_qualified_name());
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void CallbackIsolatedAgnocastExecutor::remove_node(rclcpp::Node::SharedPtr node_ptr, bool notify)
{
  remove_node(node_ptr->get_node_base_interface(), notify);
}

}  // namespace agnocast

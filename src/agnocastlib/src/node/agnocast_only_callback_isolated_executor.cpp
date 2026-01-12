#include "agnocast/node/agnocast_only_callback_isolated_executor.hpp"

#include "agnocast/agnocast.hpp"
#include "agnocast/node/agnocast_node.hpp"
#include "agnocast/node/agnocast_only_single_threaded_executor.hpp"
#include "cie_thread_configurator/cie_thread_configurator.hpp"

#include <sys/syscall.h>
#include <unistd.h>

namespace agnocast
{

AgnocastOnlyCallbackIsolatedExecutor::AgnocastOnlyCallbackIsolatedExecutor(int next_exec_timeout_ms)
: next_exec_timeout_ms_(next_exec_timeout_ms)
{
}

void AgnocastOnlyCallbackIsolatedExecutor::spin()
{
  if (spinning_.exchange(true)) {
    RCLCPP_ERROR(logger, "spin() called while already spinning");
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }

  RCPPUTILS_SCOPE_EXIT(this->spinning_.store(false););

  std::vector<std::thread> threads;
  std::vector<std::pair<
    rclcpp::CallbackGroup::SharedPtr, rclcpp::node_interfaces::NodeBaseInterface::SharedPtr>>
    groups_and_nodes;

  {
    std::lock_guard<std::mutex> guard{mutex_};

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

  std::mutex client_publisher_mutex;
  auto client_publisher = cie_thread_configurator::create_client_publisher();
  threads.reserve(groups_and_nodes.size());

  for (auto & [group, node] : groups_and_nodes) {
    auto agnocast_topics = agnocast::get_agnocast_topics_by_group(group);
    auto callback_group_id =
      cie_thread_configurator::create_callback_group_id(group, node, agnocast_topics);

    auto agnocast_executor =
      std::make_shared<AgnocastOnlySingleThreadedExecutor>(next_exec_timeout_ms_);
    agnocast_executor->dedicate_to_callback_group(group, node);

    threads.emplace_back([executor = std::move(agnocast_executor),
                          callback_group_id = std::move(callback_group_id), &client_publisher,
                          &client_publisher_mutex]() {
      auto tid = static_cast<pid_t>(syscall(SYS_gettid));

      {
        std::lock_guard<std::mutex> lock{client_publisher_mutex};
        cie_thread_configurator::publish_callback_group_info(
          client_publisher, tid, callback_group_id);
      }

      executor->spin();
    });
  }

  for (auto & thread : threads) {
    if (thread.joinable()) {
      thread.join();
    }
  }
}

void AgnocastOnlyCallbackIsolatedExecutor::add_node(
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify)
{
  (void)notify;

  std::lock_guard<std::mutex> guard{mutex_};

  std::weak_ptr<rclcpp::node_interfaces::NodeBaseInterface> weak_node_ptr = node_ptr;

  auto insert_info = weak_nodes_.insert(weak_node_ptr);
  if (!insert_info.second) {
    RCLCPP_ERROR(
      logger, "Node already exists in the executor: %s", node_ptr->get_fully_qualified_name());
    close(agnocast_fd);
    exit(EXIT_FAILURE);
  }
}

void AgnocastOnlyCallbackIsolatedExecutor::add_node(
  agnocast::Node::SharedPtr node_ptr, bool notify)
{
  add_node(node_ptr->get_node_base_interface(), notify);
}

}  // namespace agnocast

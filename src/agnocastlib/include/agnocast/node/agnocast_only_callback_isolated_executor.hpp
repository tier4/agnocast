#pragma once

#include "agnocast/node/agnocast_node.hpp"
#include "agnocast/node/agnocast_only_executor.hpp"
#include "rclcpp/rclcpp.hpp"

#include <atomic>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <vector>

namespace agnocast
{

class Node;
class AgnocastOnlySingleThreadedExecutor;

class AgnocastOnlyCallbackIsolatedExecutor : public AgnocastOnlyExecutor
{
  RCLCPP_DISABLE_COPY(AgnocastOnlyCallbackIsolatedExecutor)

  const int next_exec_timeout_ms_;

  std::mutex mutex_;

  // Nodes associated with this AgnocastOnlyCallbackIsolatedExecutor, appended by add_node() and
  // removed by remove_node()
  std::set<
    rclcpp::node_interfaces::NodeBaseInterface::WeakPtr,
    std::owner_less<rclcpp::node_interfaces::NodeBaseInterface::WeakPtr>>
    weak_nodes_ RCPPUTILS_TSA_GUARDED_BY(mutex_);

public:
  RCLCPP_PUBLIC
  explicit AgnocastOnlyCallbackIsolatedExecutor(int next_exec_timeout_ms = 50);

  RCLCPP_PUBLIC
  void spin() override;

  RCLCPP_PUBLIC
  void add_node(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify = false);

  RCLCPP_PUBLIC
  void add_node(agnocast::Node::SharedPtr node_ptr, bool notify = false);
};

}  // namespace agnocast

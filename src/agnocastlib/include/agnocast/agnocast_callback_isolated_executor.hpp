#pragma once
#include "agnocast/agnocast_executor.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

class CallbackIsolatedAgnocastExecutor : public rclcpp::Executor
{
  RCLCPP_DISABLE_COPY(CallbackIsolatedAgnocastExecutor)

  // Nodes associated with this AgnocastCallbackIsolatedExecutor, appended by add_node() and removed
  // by remove_node()
  std::set<
    rclcpp::node_interfaces::NodeBaseInterface::WeakPtr,
    std::owner_less<rclcpp::node_interfaces::NodeBaseInterface::WeakPtr>>
    weak_nodes_ RCPPUTILS_TSA_GUARDED_BY(mutex_);

  // CallbackGroups (and their belonging nodes) associated with this
  // AgnocastCallbackIsolatedExecutor, appended by add_callback_group() and removed by
  // remove_callback_group()
  std::map<
    rclcpp::CallbackGroup::WeakPtr, rclcpp::node_interfaces::NodeBaseInterface::WeakPtr,
    std::owner_less<rclcpp::CallbackGroup::WeakPtr>>
    weak_groups_to_nodes_ RCPPUTILS_TSA_GUARDED_BY(mutex_);

  std::vector<rclcpp::CallbackGroup::WeakPtr> get_manually_added_callback_groups_internal() const
    RCPPUTILS_TSA_REQUIRES(mutex_);

  std::vector<rclcpp::CallbackGroup::WeakPtr>
  get_automatically_added_callback_groups_from_nodes_internal() const
    RCPPUTILS_TSA_REQUIRES(mutex_);

public:
  RCLCPP_PUBLIC
  explicit CallbackIsolatedAgnocastExecutor(
    const rclcpp::ExecutorOptions & options = rclcpp::ExecutorOptions());

  RCLCPP_PUBLIC
  void spin() override;

  RCLCPP_PUBLIC
  void add_callback_group(
    rclcpp::CallbackGroup::SharedPtr group_ptr,
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify = true) override;

  RCLCPP_PUBLIC
  std::vector<rclcpp::CallbackGroup::WeakPtr> get_all_callback_groups() override;

  RCLCPP_PUBLIC
  std::vector<rclcpp::CallbackGroup::WeakPtr> get_manually_added_callback_groups() override;

  RCLCPP_PUBLIC
  std::vector<rclcpp::CallbackGroup::WeakPtr> get_automatically_added_callback_groups_from_nodes()
    override;

  RCLCPP_PUBLIC
  void remove_callback_group(
    rclcpp::CallbackGroup::SharedPtr group_ptr, bool notify = true) override;

  RCLCPP_PUBLIC
  void add_node(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify = true) override;

  RCLCPP_PUBLIC
  void add_node(rclcpp::Node::SharedPtr node_ptr, bool notify = true) override;

  RCLCPP_PUBLIC
  void remove_node(
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_ptr, bool notify = true) override;

  RCLCPP_PUBLIC
  void remove_node(rclcpp::Node::SharedPtr node_ptr, bool notify = true) override;
};

}  // namespace agnocast

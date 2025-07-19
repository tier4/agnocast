#pragma once
#include "agnocast/agnocast_executor.hpp"
#include "rclcpp/rclcpp.hpp"

namespace agnocast
{

class CallbackIsolatedAgnocastExecutor : public rclcpp::Executor
{
  RCLCPP_DISABLE_COPY(CallbackIsolatedAgnocastExecutor)

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

// Copyright 2025 Agnocast Contributors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef AGNOCAST__NODE_INTERFACES__NODE_BASE_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_BASE_HPP_

#include <memory>
#include <string>
#include <vector>

#include "agnocast/node_interfaces/node_base_interface.hpp"
#include "rclcpp/callback_group.hpp"

namespace agnocast
{
namespace node_interfaces
{

/// Implementation of the NodeBase part of the Node API.
class NodeBase : public NodeBaseInterface, public std::enable_shared_from_this<NodeBase>
{
public:
  using SharedPtr = std::shared_ptr<NodeBase>;
  using WeakPtr = std::weak_ptr<NodeBase>;

  /**
   * @brief Construct a NodeBase.
   *
   * @param node_name Node name
   * @param ns Namespace (default: "")
   */
  NodeBase(
    const std::string & node_name,
    const std::string & ns);

  virtual ~NodeBase() = default;

  std::string
  get_name() const override;

  std::string
  get_namespace() const override;

  std::string
  get_fully_qualified_name() const override;

  rclcpp::CallbackGroup::SharedPtr
  create_callback_group(
    rclcpp::CallbackGroupType group_type,
    bool automatically_add_to_executor_with_node = true) override;

  rclcpp::CallbackGroup::SharedPtr
  get_default_callback_group() override;

  bool
  callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & group) override;

private:
  std::string node_name_;
  std::string namespace_;
  rclcpp::CallbackGroup::SharedPtr default_callback_group_;
  std::vector<rclcpp::CallbackGroup::WeakPtr> callback_groups_;
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_BASE_HPP_

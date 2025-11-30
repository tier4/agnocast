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

#ifndef AGNOCAST__NODE_INTERFACES__NODE_BASE_INTERFACE_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_BASE_INTERFACE_HPP_

#include <memory>
#include <string>
#include <vector>

#include "rclcpp/callback_group.hpp"

namespace agnocast
{
namespace node_interfaces
{

/// Pure virtual interface class for the NodeBase part of the Node API.
class NodeBaseInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeBaseInterface>;
  using WeakPtr = std::weak_ptr<NodeBaseInterface>;

  virtual ~NodeBaseInterface() = default;

  /// Return the name of the node.
  /** \return The name of the node. */
  virtual
  std::string
  get_name() const = 0;

  /// Return the namespace of the node.
  /** \return The namespace of the node. */
  virtual
  std::string
  get_namespace() const = 0;

  /// Return the fully qualified name of the node.
  /** \return The fully qualified name of the node. */
  virtual
  std::string
  get_fully_qualified_name() const = 0;

  /// Create and return a callback group.
  virtual
  rclcpp::CallbackGroup::SharedPtr
  create_callback_group(
    rclcpp::CallbackGroupType group_type,
    bool automatically_add_to_executor_with_node = true) = 0;

  /// Return the default callback group.
  virtual
  rclcpp::CallbackGroup::SharedPtr
  get_default_callback_group() = 0;

  /// Return true if the given callback group is associated with this node.
  virtual
  bool
  callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & group) = 0;
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_BASE_INTERFACE_HPP_

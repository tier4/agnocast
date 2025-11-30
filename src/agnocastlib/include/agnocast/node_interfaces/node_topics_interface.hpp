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

#ifndef AGNOCAST__NODE_INTERFACES__NODE_TOPICS_INTERFACE_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_TOPICS_INTERFACE_HPP_

#include <memory>
#include <string>

namespace agnocast
{
namespace node_interfaces
{

/// Pure virtual interface class for the NodeTopics part of the Node API.
class NodeTopicsInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTopicsInterface>;
  using WeakPtr = std::weak_ptr<NodeTopicsInterface>;

  virtual ~NodeTopicsInterface() = default;

  /// Resolve a topic name using node namespace and remapping rules.
  /**
   * Corresponds to rcl_node_resolve_name in rcl/src/rcl/node_resolve_name.c:134-162.
   *
   * \param input_topic_name Topic name to resolve
   * \return Resolved topic name
   */
  virtual
  std::string
  resolve_topic_name(const std::string & input_topic_name) const = 0;
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_TOPICS_INTERFACE_HPP_

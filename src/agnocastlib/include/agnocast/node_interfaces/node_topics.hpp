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

#ifndef AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_
#define AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_

#include "agnocast/agnocast_context.hpp"
#include "agnocast/node_interfaces/node_topics_interface.hpp"
#include "rclcpp/node_interfaces/node_base_interface.hpp"

#include <memory>
#include <string>
#include <vector>

namespace agnocast
{
namespace node_interfaces
{

/// Implementation of the NodeTopics part of the Node API.
class NodeTopics : public NodeTopicsInterface
{
public:
  using SharedPtr = std::shared_ptr<NodeTopics>;
  using WeakPtr = std::weak_ptr<NodeTopics>;

  /**
   * @brief Construct a NodeTopics.
   *
   * @param node_base Pointer to the node base interface
   */
  explicit NodeTopics(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base);

  virtual ~NodeTopics() = default;

  std::string resolve_topic_name(const std::string & input_topic_name) const override;

  /**
   * @brief Add a remap rule for topic remapping.
   *
   * @param rule Remap rule to add
   */
  void add_remap_rule(const RemapRule & rule);

  /**
   * @brief Get all topic remap rules.
   *
   * @return Vector of remap rules
   */
  const std::vector<RemapRule> & get_remap_rules() const;

private:
  /**
   * @brief Resolve a name (main implementation).
   *
   * Calls expand_topic_name then remap_name.
   * Corresponds to rcl_resolve_name in rcl/src/rcl/node_resolve_name.c.
   *
   * @param input_topic_name Topic name to resolve
   * @return Resolved topic name
   */
  std::string resolve_name(const std::string & input_topic_name) const;

  /**
   * @brief Expand a topic name (handle substitutions, private/relative/absolute).
   *
   * Corresponds to rcl_expand_topic_name in rcl/src/rcl/expand_topic_name.c.
   *
   * @param input_topic_name Topic name to expand
   * @return Expanded topic name
   */
  std::string expand_topic_name(const std::string & input_topic_name) const;

  /**
   * @brief Apply remapping to a topic name.
   *
   * Corresponds to rcl_remap_name in rcl/src/rcl/remap.c.
   *
   * @param name Name to remap
   * @return Remapped name (or original if no remapping exists)
   */
  std::string remap_name(const std::string & name) const;

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base_;
  std::vector<RemapRule> remap_rules_;  // Only TOPIC type rules
};

}  // namespace node_interfaces
}  // namespace agnocast

#endif  // AGNOCAST__NODE_INTERFACES__NODE_TOPICS_HPP_

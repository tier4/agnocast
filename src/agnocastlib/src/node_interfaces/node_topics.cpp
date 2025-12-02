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

#include "agnocast/node_interfaces/node_topics.hpp"

namespace agnocast
{
namespace node_interfaces
{

NodeTopics::NodeTopics(rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base)
: node_base_(node_base)
{
}

std::string NodeTopics::resolve_topic_name(const std::string & input_topic_name) const
{
  // Corresponds to rcl_node_resolve_name in rcl/src/rcl/node_resolve_name.c:134-162
  return resolve_name(input_topic_name);
}

void NodeTopics::add_remap_rule(const RemapRule & rule)
{
  if (rule.type == RemapType::TOPIC) {
    remap_rules_.push_back(rule);
  }
}

const std::vector<RemapRule> & NodeTopics::get_remap_rules() const
{
  return remap_rules_;
}

std::string NodeTopics::resolve_name(const std::string & input_topic_name) const
{
  // Corresponds to rcl_resolve_name in rcl/src/rcl/node_resolve_name.c:32-131
  // Variable names match rcl/src/rcl/node_resolve_name.c:57-58
  // Two-step process:
  // 1. Expand topic name (handle ~, {node}, {ns}, relative/absolute paths)
  // 2. Apply remapping rules (--ros-args -r old:=new)
  std::string expanded_topic_name = expand_topic_name(input_topic_name);
  std::string remapped_topic_name = remap_name(expanded_topic_name);
  return remapped_topic_name;
}

std::string NodeTopics::expand_topic_name(const std::string & input_topic_name) const
{
  // Corresponds to rcl_expand_topic_name in rcl/src/rcl/expand_topic_name.c:44-219
  // Handles:
  // - Private topics: "~foo" -> "/namespace/node_name/foo"
  // - Substitutions: "{node}" -> node_name, "{ns}" or "{namespace}" -> namespace
  // - Relative topics: "foo" -> "/namespace/foo"
  // - Absolute topics: "/foo" -> "/foo" (unchanged)

  if (input_topic_name.empty()) {
    return input_topic_name;
  }

  std::string local_output = input_topic_name;
  std::string node_name = node_base_->get_name();
  std::string namespace_ = node_base_->get_namespace();

  // Check for substitutions in the topic name
  // Variable names match rcl/src/rcl/expand_topic_name.c:97-100
  bool has_a_substitution = input_topic_name.find('{') != std::string::npos;
  bool has_a_namespace_tilde = !input_topic_name.empty() && input_topic_name[0] == '~';
  bool is_absolute = !input_topic_name.empty() && input_topic_name[0] == '/';

  // If absolute and no substitution, return as-is (rcl:102-110)
  if (is_absolute && !has_a_substitution) {
    return input_topic_name;
  }

  // Handle private topic name (starts with '~') (rcl:113-125)
  // Replace ~ with namespace/node_name
  if (has_a_namespace_tilde) {
    // Special case: namespace is "/" (rcl:117)
    if (namespace_.empty() || namespace_ == "/") {
      local_output = "/" + node_name + input_topic_name.substr(1);
    } else {
      local_output = namespace_ + "/" + node_name + input_topic_name.substr(1);
    }
  }

  // Handle substitutions ({node}, {ns}, {namespace}) (rcl:127-194)
  if (has_a_substitution) {
    size_t pos = 0;
    while ((pos = local_output.find('{', pos)) != std::string::npos) {
      size_t end_pos = local_output.find('}', pos);
      if (end_pos == std::string::npos) {
        break;  // Malformed substitution
      }

      std::string substitution = local_output.substr(pos, end_pos - pos + 1);
      std::string replacement;

      // rcl:144-150
      if (substitution == "{node}") {
        replacement = node_name;
      } else if (substitution == "{ns}" || substitution == "{namespace}") {
        replacement = namespace_;
      }
      // Unknown substitutions are left as-is

      if (!replacement.empty()) {
        local_output.replace(pos, substitution.length(), replacement);
        pos += replacement.length();
      } else {
        pos = end_pos + 1;
      }
    }
  }

  // Make relative topic names absolute by prepending namespace (rcl:196-215)
  if (!local_output.empty() && local_output[0] != '/') {
    if (namespace_.empty() || namespace_ == "/") {
      local_output = "/" + local_output;
    } else {
      local_output = namespace_ + "/" + local_output;
    }
  }

  return local_output;
}

std::string NodeTopics::remap_name(const std::string & name) const
{
  // Corresponds to rcl_remap_name in rcl/src/rcl/remap.c:167-231
  // Variable names match rcl/src/rcl/remap.c:171 (name) and remap.c:129 (expanded_match)
  //
  // RCL expands the match side before comparing (remap.c:128-132)
  // Example: --ros-args -r foo:=/bar will map "foo" -> "/bar"
  // The "from" side is expanded before matching, so "foo" becomes "/namespace/foo"

  for (const auto & rule : remap_rules_) {
    // Only apply TOPIC remap rules (should already be filtered, but double-check)
    if (rule.type != RemapType::TOPIC) {
      continue;
    }

    // Expand the match side and compare
    std::string expanded_match = expand_topic_name(rule.match);
    if (expanded_match == name) {
      return rule.replacement;
    }
  }
  return name;
}

}  // namespace node_interfaces
}  // namespace agnocast

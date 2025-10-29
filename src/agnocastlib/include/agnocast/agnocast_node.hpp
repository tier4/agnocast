#pragma once

#include <map>
#include <memory>
#include <string>
#include <variant>
#include <vector>

namespace agnocast
{

/**
 * @brief Lightweight node class for Agnocast.
 *
 * This class provides minimal ROS 2 node functionality without creating
 * a DDS participant. It parses command-line arguments to extract node
 * configuration and supports topic name resolution and parameter access.
 */
class Node
{
public:
  using SharedPtr = std::shared_ptr<Node>;
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  /**
   * @brief Construct a Node by parsing command-line arguments.
   *
   * @param argc Argument count from main()
   * @param argv Argument vector from main()
   * @param default_node_name Default node name if not remapped
   * @param default_namespace Default namespace if not specified (default: "")
   */
  Node(
    int argc, char * argv[], const std::string & default_node_name,
    const std::string & default_namespace = "");

  /**
   * @brief Construct a Node with explicit values (no argument parsing).
   *
   * @param node_name Node name
   * @param namespace_ Namespace (default: "")
   */
  Node(const std::string & node_name, const std::string & namespace_ = "");

  /**
   * @brief Get the node name.
   * @return Node name
   */
  std::string get_name() const { return node_name_; }

  /**
   * @brief Get the namespace.
   * @return Namespace
   */
  std::string get_namespace() const { return namespace_; }

  /**
   * @brief Get the fully qualified name of the node.
   * @return Fully qualified node name (namespace/node_name)
   */
  std::string get_fully_qualified_name() const;

  /**
   * @brief Resolve a topic name to its fully qualified form.
   *
   * Applies topic remapping rules and namespace resolution.
   *
   * @param topic_name Topic name to resolve
   * @return Fully qualified topic name
   */
  std::string resolve_topic_name(const std::string & topic_name) const;

  /**
   * @brief Get a parameter value.
   *
   * @param name Parameter name
   * @param value Output parameter value
   * @return true if parameter exists, false otherwise
   */
  bool get_parameter(const std::string & name, bool & value) const;
  bool get_parameter(const std::string & name, int64_t & value) const;
  bool get_parameter(const std::string & name, double & value) const;
  bool get_parameter(const std::string & name, std::string & value) const;

private:
  /**
   * @brief Parse ROS arguments from argc/argv.
   *
   * Extracts namespace, node name remapping, topic remappings, and parameters.
   *
   * @param argc Argument count
   * @param argv Argument vector
   */
  void parse_ros_args(int argc, char * argv[]);

  /**
   * @brief Apply remapping to a topic name.
   *
   * @param topic_name Topic name to remap
   * @return Remapped topic name (or original if no remapping exists)
   */
  std::string apply_remapping(const std::string & topic_name) const;

  /**
   * @brief Parse a parameter value string to appropriate type.
   *
   * @param value_str String representation of the value
   * @return Parsed parameter value
   */
  ParameterValue parse_parameter_value(const std::string & value_str) const;

  std::string node_name_;
  std::string namespace_;
  std::map<std::string, std::string> topic_remappings_;
  std::map<std::string, ParameterValue> parameters_;
};

}  // namespace agnocast

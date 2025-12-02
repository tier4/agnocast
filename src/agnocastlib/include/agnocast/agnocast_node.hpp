#pragma once

#include "agnocast/agnocast_context.hpp"
#include "agnocast/agnocast_subscription.hpp"
#include "rclcpp/node_options.hpp"
#include "rclcpp/rclcpp.hpp"

#include <map>
#include <memory>
#include <string>
#include <variant>
#include <vector>

// New node interfaces (now inherit from rclcpp interfaces)
#include "agnocast/node_interfaces/node_base.hpp"
#include "agnocast/node_interfaces/node_parameters.hpp"
#include "agnocast/node_interfaces/node_topics.hpp"

namespace agnocast
{

// Parameter type constants (from rcl_interfaces/msg/ParameterType)
// Corresponds to ParameterType constants in ROS 2
// See: rcl_interfaces/msg/ParameterType.msg
constexpr uint8_t PARAMETER_NOT_SET = 0;
constexpr uint8_t PARAMETER_BOOL = 1;
constexpr uint8_t PARAMETER_INTEGER = 2;
constexpr uint8_t PARAMETER_DOUBLE = 3;
constexpr uint8_t PARAMETER_STRING = 4;
// Note: Array types (5-8) are not supported in agnocast

/**
 * @brief Simplified parameter descriptor (subset of rcl_interfaces::msg::ParameterDescriptor).
 */
struct ParameterDescriptor
{
  std::string description;
  bool read_only = false;
};

/**
 * @brief Internal struct for holding parameter information.
 */
struct ParameterInfo
{
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  ParameterValue value;
  ParameterDescriptor descriptor;
};

/**
 * @brief Lightweight node class for Agnocast.
 *
 * This class provides minimal ROS 2 node functionality without creating
 * a DDS participant. It parses command-line arguments to extract node
 * configuration and supports topic name resolution and parameter access.
 *
 * The node is composed of three main interfaces:
 * - NodeBase: Basic node identity (name, namespace, callback groups)
 * - NodeTopics: Topic name resolution and remapping
 * - NodeParameters: Parameter management
 */
class Node
{
public:
  using SharedPtr = std::shared_ptr<Node>;
  using ParameterValue = std::variant<bool, int64_t, double, std::string>;

  /**
   * @brief Default constructor that queries node name from Context.
   *
   * This constructor is for backward compatibility with code that expects
   * node name to be set via command-line arguments (--ros-args -r __node:=name).
   */
  Node();

  /**
   * @brief Construct a Node with explicit values.
   *
   * @param node_name Node name
   * @param namespace_ Namespace (default: "")
   *
   * @note Command-line argument parsing should be done via agnocast::init(argc, argv)
   *       before constructing the Node. This matches rclcpp::Node's design.
   */
  Node(const std::string & node_name, const std::string & namespace_ = "");

  /**
   * @brief Construct a Node from NodeOptions (Composable Node support).
   *
   * This constructor is required for registering the node as a Composable Node
   * using RCLCPP_COMPONENTS_REGISTER_NODE macro.
   *
   * @param options rclcpp::NodeOptions containing:
   *   - Node name and namespace (extracted from arguments())
   *   - rclcpp::Context (from context())
   *   - Parameter overrides (from parameter_overrides())
   *
   * @note The node name and namespace are extracted from the arguments using
   *       --ros-args -r __node:=name and -r __ns:=namespace patterns.
   */
  explicit Node(const rclcpp::NodeOptions & options);

  /**
   * @brief Get the node name.
   *
   * Corresponds to rcl_node_get_name in rcl/src/rcl/node.c:435-441.
   *
   * @return Node name
   */
  std::string get_name() const { return node_base_->get_name(); }

  /**
   * @brief Get the logger for this node.
   *
   * @return Logger instance
   */
  rclcpp::Logger get_logger() const { return logger_; }

  /**
   * @brief Get the namespace.
   *
   * Corresponds to rcl_node_get_namespace in rcl/src/rcl/node.c:444-450.
   *
   * @return Namespace
   */
  std::string get_namespace() const { return node_base_->get_namespace(); }

  /**
   * @brief Get the fully qualified name of the node.
   *
   * Corresponds to rcl_node_get_fully_qualified_name in rcl/src/rcl/node.c:453-459.
   *
   * @return Fully qualified node name (namespace/node_name)
   */
  std::string get_fully_qualified_name() const { return node_base_->get_fully_qualified_name(); }

  /**
   * @brief Get the default callback group.
   *
   * @return Shared pointer to the default callback group
   */
  rclcpp::CallbackGroup::SharedPtr get_default_callback_group()
  {
    return node_base_->get_default_callback_group();
  }

  /**
   * @brief Create and return a callback group.
   */
  rclcpp::CallbackGroup::SharedPtr create_callback_group(
    rclcpp::CallbackGroupType group_type, bool automatically_add_to_executor_with_node = true)
  {
    return node_base_->create_callback_group(group_type, automatically_add_to_executor_with_node);
  }

  /**
   * @brief Check if a callback group belongs to this node.
   *
   * @param group Callback group to check
   * @return true if the callback group belongs to this node, false otherwise
   */
  bool callback_group_in_node(const rclcpp::CallbackGroup::SharedPtr & group)
  {
    return node_base_->callback_group_in_node(group);
  }

  /**
   * @brief Resolve a topic name to its fully qualified form.
   *
   * Applies topic remapping rules and namespace resolution.
   * Corresponds to rcl_node_resolve_name in rcl/src/rcl/node_resolve_name.c:134-162.
   * Delegates to resolve_name which calls expand_topic_name then remap_name.
   *
   * @param input_topic_name Topic name to resolve
   * @return Fully qualified topic name
   */
  std::string resolve_topic_name(const std::string & input_topic_name) const
  {
    return node_topics_->resolve_topic_name(input_topic_name);
  }

  /**
   * @brief Declare a parameter with a default value.
   *
   * Corresponds to NodeParameters::declare_parameter in
   * rclcpp/src/rclcpp/node_interfaces/node_parameters.cpp.
   * Supports command-line parameter overrides.
   *
   * @param name Parameter name
   * @param default_value Default parameter value
   * @param descriptor Parameter descriptor (default: empty)
   * @param ignore_override If true, ignore command-line overrides (default: false)
   * @return Reference to the parameter value (either override or default)
   */
  const ParameterValue & declare_parameter(
    const std::string & name, const ParameterValue & default_value,
    const ParameterDescriptor & descriptor = ParameterDescriptor{}, bool ignore_override = false);

  /**
   * @brief Check if a parameter has been declared.
   *
   * Corresponds to NodeParameters::has_parameter in
   * rclcpp/include/rclcpp/node_interfaces/node_parameters.hpp:130.
   *
   * @param name Parameter name
   * @return true if parameter exists, false otherwise
   */
  bool has_parameter(const std::string & name) const
  {
    return node_parameters_->has_parameter(name);
  }

  /**
   * @brief Get parameter types for a list of parameter names.
   *
   * Corresponds to NodeParameters::get_parameter_types in
   * rclcpp/include/rclcpp/node_interfaces/node_parameters.hpp:168.
   *
   * @param names Vector of parameter names
   * @return Vector of parameter types using PARAMETER_* constants:
   *   - PARAMETER_NOT_SET (0): Parameter not found or not set
   *   - PARAMETER_BOOL (1): Boolean parameter
   *   - PARAMETER_INTEGER (2): Integer parameter (int64_t)
   *   - PARAMETER_DOUBLE (3): Double parameter
   *   - PARAMETER_STRING (4): String parameter
   */
  std::vector<uint8_t> get_parameter_types(const std::vector<std::string> & names) const
  {
    return node_parameters_->get_parameter_types(names);
  }

  /**
   * @brief Get a parameter value.
   *
   * Corresponds to NodeParameters::get_parameter in
   * rclcpp/src/rclcpp/node_interfaces/node_parameters.cpp:829-845.
   *
   * @param name Parameter name
   * @param value Output parameter value
   * @return true if parameter exists, false otherwise
   */
  bool get_parameter(const std::string & name, bool & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_BOOL) {
      return false;
    }
    value = param.as_bool();
    return true;
  }

  bool get_parameter(const std::string & name, int64_t & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_INTEGER) {
      return false;
    }
    value = param.as_int();
    return true;
  }

  bool get_parameter(const std::string & name, double & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_DOUBLE) {
      return false;
    }
    value = param.as_double();
    return true;
  }

  bool get_parameter(const std::string & name, std::string & value) const
  {
    rclcpp::Parameter param;
    if (!node_parameters_->get_parameter(name, param)) {
      return false;
    }
    if (param.get_type() != rclcpp::ParameterType::PARAMETER_STRING) {
      return false;
    }
    value = param.as_string();
    return true;
  }

  /**
   * @brief Return the Node's internal NodeBaseInterface implementation.
   *
   * This method is required for Composable Node support.
   * For composable nodes, ensure that a valid rclcpp::Context is available
   * (either through NodeOptions or rclcpp::init()).
   */
  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr get_node_base_interface()
  {
    return node_base_;
  }

  /**
   * @brief Return the Node's internal NodeTopicsInterface implementation.
   */
  rclcpp::node_interfaces::NodeTopicsInterface::SharedPtr get_node_topics_interface()
  {
    return node_topics_;
  }

  /**
   * @brief Return the Node's internal NodeParametersInterface implementation.
   */
  rclcpp::node_interfaces::NodeParametersInterface::SharedPtr get_node_parameters_interface()
  {
    return node_parameters_;
  }

  /**
   * @brief Create a subscription (member function template).
   *
   * This is a convenience method that wraps the global create_subscription function.
   * The actual implementation is deferred to avoid circular dependencies.
   *
   * @tparam MessageT Message type
   * @tparam Func Callback function type
   * @param topic_name Topic name
   * @param queue_size Queue size
   * @param callback Callback function
   * @param options Subscription options
   * @return Shared pointer to the subscription
   */
  template <typename MessageT, typename Func>
  typename Subscription<MessageT>::SharedPtr create_subscription(
    const std::string & topic_name, size_t queue_size, Func && callback,
    SubscriptionOptions options);

private:
  void initialize_node(const std::string & node_name, const std::string & ns);

  rclcpp::Logger logger_{rclcpp::get_logger("agnocast_node")};
  node_interfaces::NodeBase::SharedPtr node_base_;
  node_interfaces::NodeTopics::SharedPtr node_topics_;
  node_interfaces::NodeParameters::SharedPtr node_parameters_;
};

}  // namespace agnocast

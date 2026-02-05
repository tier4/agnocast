#include "agnocast/node/agnocast_node.hpp"
#include "rclcpp/rclcpp.hpp"
#include "rclcpp/version.h"

#include <gtest/gtest.h>

class TestNodeBase : public ::testing::Test
{
protected:
  void SetUp() override {}

  void TearDown() override {}

  agnocast::Node::SharedPtr node_;

  rclcpp::node_interfaces::NodeBaseInterface::SharedPtr create_node_base(
    const std::string & node_name, const std::string & node_namespace)
  {
    node_ = std::make_shared<agnocast::Node>(node_name, node_namespace);
    return node_->get_node_base_interface();
  }
};

// =========================================
// Basic construction and name tests
// =========================================

TEST_F(TestNodeBase, get_name)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_STREQ("my_node", node_base->get_name());
}

TEST_F(TestNodeBase, get_namespace_with_leading_slash)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_STREQ("/my_ns", node_base->get_namespace());
}

TEST_F(TestNodeBase, get_namespace_without_leading_slash)
{
  auto node_base = create_node_base("my_node", "my_ns");
  // NodeBase automatically adds leading slash if missing
  EXPECT_STREQ("/my_ns", node_base->get_namespace());
}

TEST_F(TestNodeBase, get_namespace_empty)
{
  auto node_base = create_node_base("my_node", "");
  // Empty namespace becomes root "/"
  EXPECT_STREQ("/", node_base->get_namespace());
}

TEST_F(TestNodeBase, get_namespace_root)
{
  auto node_base = create_node_base("my_node", "/");
  EXPECT_STREQ("/", node_base->get_namespace());
}

TEST_F(TestNodeBase, get_fully_qualified_name)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_STREQ("/my_ns/my_node", node_base->get_fully_qualified_name());
}

TEST_F(TestNodeBase, get_fully_qualified_name_root_namespace)
{
  auto node_base = create_node_base("my_node", "/");
  EXPECT_STREQ("/my_node", node_base->get_fully_qualified_name());
}

TEST_F(TestNodeBase, get_fully_qualified_name_nested_namespace)
{
  auto node_base = create_node_base("my_node", "/ns1/ns2/ns3");
  EXPECT_STREQ("/ns1/ns2/ns3/my_node", node_base->get_fully_qualified_name());
}

// =========================================
// Context tests
// =========================================

TEST_F(TestNodeBase, get_context_standalone_node)
{
  // For standalone agnocast nodes (without rclcpp::init()), context may be nullptr
  auto node_base = create_node_base("my_node", "/my_ns");
  // Context might be nullptr for standalone nodes - this is expected behavior
  // Just verify the method doesn't crash
  auto context = node_base->get_context();
  // The context could be nullptr or valid depending on initialization state
  (void)context;
}

// =========================================
// RCL node handle tests (should throw)
// =========================================

TEST_F(TestNodeBase, get_rcl_node_handle_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(node_base->get_rcl_node_handle(), std::runtime_error);
}

TEST_F(TestNodeBase, get_rcl_node_handle_const_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  const auto * const_node_base = node_base.get();
  EXPECT_THROW(const_node_base->get_rcl_node_handle(), std::runtime_error);
}

TEST_F(TestNodeBase, get_shared_rcl_node_handle_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(node_base->get_shared_rcl_node_handle(), std::runtime_error);
}

TEST_F(TestNodeBase, get_shared_rcl_node_handle_const_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  const auto * const_node_base = node_base.get();
  EXPECT_THROW(const_node_base->get_shared_rcl_node_handle(), std::runtime_error);
}

// =========================================
// Callback group tests
// =========================================

TEST_F(TestNodeBase, get_default_callback_group)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto default_group = node_base->get_default_callback_group();
  EXPECT_NE(nullptr, default_group);
}

TEST_F(TestNodeBase, get_default_callback_group_type_is_mutually_exclusive)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto default_group = node_base->get_default_callback_group();
  EXPECT_EQ(rclcpp::CallbackGroupType::MutuallyExclusive, default_group->type());
}

TEST_F(TestNodeBase, create_callback_group_mutually_exclusive)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto group = node_base->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  EXPECT_NE(nullptr, group);
  EXPECT_EQ(rclcpp::CallbackGroupType::MutuallyExclusive, group->type());
}

TEST_F(TestNodeBase, create_callback_group_reentrant)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto group = node_base->create_callback_group(rclcpp::CallbackGroupType::Reentrant);
  EXPECT_NE(nullptr, group);
  EXPECT_EQ(rclcpp::CallbackGroupType::Reentrant, group->type());
}

TEST_F(TestNodeBase, create_callback_group_automatically_add_to_executor_true)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto group = node_base->create_callback_group(
    rclcpp::CallbackGroupType::MutuallyExclusive, true);
  EXPECT_NE(nullptr, group);
  EXPECT_TRUE(group->automatically_add_to_executor_with_node());
}

TEST_F(TestNodeBase, create_callback_group_automatically_add_to_executor_false)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto group = node_base->create_callback_group(
    rclcpp::CallbackGroupType::MutuallyExclusive, false);
  EXPECT_NE(nullptr, group);
  EXPECT_FALSE(group->automatically_add_to_executor_with_node());
}

TEST_F(TestNodeBase, callback_group_in_node_default_group)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto default_group = node_base->get_default_callback_group();
  EXPECT_TRUE(node_base->callback_group_in_node(default_group));
}

TEST_F(TestNodeBase, callback_group_in_node_created_group)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto group = node_base->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  EXPECT_TRUE(node_base->callback_group_in_node(group));
}

TEST_F(TestNodeBase, callback_group_in_node_external_group_returns_false)
{
  auto node_base = create_node_base("my_node", "/my_ns");

  // Create a second node and get its callback group
  auto node2 = std::make_shared<agnocast::Node>("other_node", "/other_ns");
  auto other_group = node2->get_node_base_interface()->get_default_callback_group();

  // The external group should not be in this node
  EXPECT_FALSE(node_base->callback_group_in_node(other_group));
}

TEST_F(TestNodeBase, for_each_callback_group_counts_groups)
{
  auto node_base = create_node_base("my_node", "/my_ns");

  // Initially there's the default callback group
  int count = 0;
  node_base->for_each_callback_group([&count](rclcpp::CallbackGroup::SharedPtr) { ++count; });
  EXPECT_EQ(1, count);

  // Create additional callback groups
  node_base->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
  node_base->create_callback_group(rclcpp::CallbackGroupType::Reentrant);

  count = 0;
  node_base->for_each_callback_group([&count](rclcpp::CallbackGroup::SharedPtr) { ++count; });
  EXPECT_EQ(3, count);
}

TEST_F(TestNodeBase, for_each_callback_group_weak_ptr_cleanup)
{
  auto node_base = create_node_base("my_node", "/my_ns");

  // Create a callback group in a limited scope
  {
    auto group = node_base->create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);
    int count = 0;
    node_base->for_each_callback_group([&count](rclcpp::CallbackGroup::SharedPtr) { ++count; });
    EXPECT_EQ(2, count);  // default + created group
  }

  // After the group goes out of scope, for_each should only iterate valid groups
  // Note: The weak_ptr still exists in the vector, but lock() returns nullptr
  int count = 0;
  node_base->for_each_callback_group([&count](rclcpp::CallbackGroup::SharedPtr) { ++count; });
  EXPECT_EQ(1, count);  // Only default group remains valid
}

// =========================================
// Executor association tests
// =========================================

TEST_F(TestNodeBase, get_associated_with_executor_atomic_initial_false)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_FALSE(node_base->get_associated_with_executor_atomic().load());
}

TEST_F(TestNodeBase, get_associated_with_executor_atomic_can_set)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  node_base->get_associated_with_executor_atomic().store(true);
  EXPECT_TRUE(node_base->get_associated_with_executor_atomic().load());
}

// =========================================
// Guard condition tests (should throw)
// =========================================

TEST_F(TestNodeBase, get_notify_guard_condition_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(node_base->get_notify_guard_condition(), std::runtime_error);
}

// rclcpp 28+ (Jazzy) added these methods
#if RCLCPP_VERSION_MAJOR >= 28
TEST_F(TestNodeBase, get_shared_notify_guard_condition_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(node_base->get_shared_notify_guard_condition(), std::runtime_error);
}

TEST_F(TestNodeBase, trigger_notify_guard_condition_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(node_base->trigger_notify_guard_condition(), std::runtime_error);
}
#endif

// =========================================
// Intra-process and topic statistics defaults
// =========================================

TEST_F(TestNodeBase, get_use_intra_process_default)
{
  // Default is false
  auto node_base = create_node_base("my_node", "/my_ns");
  // This logs a warning but returns the value
  bool value = node_base->get_use_intra_process_default();
  EXPECT_FALSE(value);
}

TEST_F(TestNodeBase, get_use_intra_process_default_with_options_true)
{
  rclcpp::NodeOptions options;
  options.use_intra_process_comms(true);
  auto node = std::make_shared<agnocast::Node>("my_node", "/my_ns", options);
  auto node_base = node->get_node_base_interface();
  // This logs a warning but returns the value
  bool value = node_base->get_use_intra_process_default();
  EXPECT_TRUE(value);
}

TEST_F(TestNodeBase, get_enable_topic_statistics_default)
{
  // Default is false
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_FALSE(node_base->get_enable_topic_statistics_default());
}

TEST_F(TestNodeBase, get_enable_topic_statistics_default_with_options_true)
{
  rclcpp::NodeOptions options;
  options.enable_topic_statistics(true);
  auto node = std::make_shared<agnocast::Node>("my_node", "/my_ns", options);
  auto node_base = node->get_node_base_interface();
  EXPECT_TRUE(node_base->get_enable_topic_statistics_default());
}

// =========================================
// resolve_topic_or_service_name tests
// =========================================

TEST_F(TestNodeBase, resolve_topic_name_absolute)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto resolved = node_base->resolve_topic_or_service_name("/absolute_topic", false, true);
  EXPECT_EQ("/absolute_topic", resolved);
}

TEST_F(TestNodeBase, resolve_topic_name_relative)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto resolved = node_base->resolve_topic_or_service_name("relative_topic", false, true);
  EXPECT_EQ("/my_ns/relative_topic", resolved);
}

TEST_F(TestNodeBase, resolve_topic_name_tilde)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto resolved = node_base->resolve_topic_or_service_name("~/private_topic", false, true);
  EXPECT_EQ("/my_ns/my_node/private_topic", resolved);
}

TEST_F(TestNodeBase, resolve_topic_name_with_node_substitution)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto resolved = node_base->resolve_topic_or_service_name("{node}/topic", false, true);
  EXPECT_EQ("/my_ns/my_node/topic", resolved);
}

TEST_F(TestNodeBase, resolve_service_name_absolute)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto resolved = node_base->resolve_topic_or_service_name("/absolute_service", true, true);
  EXPECT_EQ("/absolute_service", resolved);
}

TEST_F(TestNodeBase, resolve_service_name_relative)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  auto resolved = node_base->resolve_topic_or_service_name("relative_service", true, true);
  EXPECT_EQ("/my_ns/relative_service", resolved);
}

TEST_F(TestNodeBase, resolve_topic_name_root_namespace)
{
  auto node_base = create_node_base("my_node", "/");
  auto resolved = node_base->resolve_topic_or_service_name("topic", false, true);
  EXPECT_EQ("/topic", resolved);
}

TEST_F(TestNodeBase, resolve_topic_name_empty_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(node_base->resolve_topic_or_service_name("", false, true), std::runtime_error);
}

TEST_F(TestNodeBase, resolve_topic_name_unknown_substitution_throws)
{
  auto node_base = create_node_base("my_node", "/my_ns");
  EXPECT_THROW(
    node_base->resolve_topic_or_service_name("{unknown}", false, true), std::runtime_error);
}

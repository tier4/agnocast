#include "agnocast/node_interfaces/node_topics.hpp"
#include "rclcpp/rclcpp.hpp"

#include <gtest/gtest.h>

using agnocast::node_interfaces::NodeTopics;

class NodeTopicsExpandTest : public ::testing::Test
{
protected:
  void SetUp() override { rclcpp::init(0, nullptr); }

  void TearDown() override { rclcpp::shutdown(); }

  NodeTopics::SharedPtr create_node_topics(
    const std::string & node_name, const std::string & node_namespace)
  {
    rclcpp::NodeOptions options;
    options.arguments({"--ros-args", "-r", "__ns:=" + node_namespace});
    auto node = std::make_shared<rclcpp::Node>(node_name, options);
    return std::make_shared<NodeTopics>(node->get_node_base_interface());
  }
};

// =========================================
// Absolute path tests
// =========================================

TEST_F(NodeTopicsExpandTest, absolute_path_no_substitution)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("/chatter", true), "/chatter");
}

TEST_F(NodeTopicsExpandTest, absolute_path_with_node_substitution)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("/{node}", true), "/my_node");
}

TEST_F(NodeTopicsExpandTest, absolute_path_with_ns_substitution)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  // {ns} is replaced with "/my_ns", so "/{ns}" becomes "//my_ns"
  // This matches RCL behavior where {ns} includes the leading slash
  EXPECT_EQ(node_topics->resolve_topic_name("/{ns}", true), "//my_ns");
}

TEST_F(NodeTopicsExpandTest, absolute_path_with_namespace_substitution)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  // {namespace} is replaced with "/my_ns", so "/{namespace}" becomes "//my_ns"
  EXPECT_EQ(node_topics->resolve_topic_name("/{namespace}", true), "//my_ns");
}

// =========================================
// Relative path tests
// =========================================

TEST_F(NodeTopicsExpandTest, relative_path_simple)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("chatter", true), "/my_ns/chatter");
}

TEST_F(NodeTopicsExpandTest, relative_path_with_node_substitution)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("{node}/chatter", true), "/my_ns/my_node/chatter");
}

TEST_F(NodeTopicsExpandTest, relative_path_node_only)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("{node}", true), "/my_ns/my_node");
}

TEST_F(NodeTopicsExpandTest, relative_path_ns_only)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  // {ns} is replaced with "/my_ns" which is already absolute, so no prefix is added
  EXPECT_EQ(node_topics->resolve_topic_name("{ns}", true), "/my_ns");
}

// =========================================
// Tilde expansion tests (private topics)
// =========================================

TEST_F(NodeTopicsExpandTest, tilde_only)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("~", true), "/my_ns/my_node");
}

TEST_F(NodeTopicsExpandTest, tilde_with_topic)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("~/ping", true), "/my_ns/my_node/ping");
}

TEST_F(NodeTopicsExpandTest, tilde_with_substitution)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_EQ(node_topics->resolve_topic_name("~/{node}", true), "/my_ns/my_node/my_node");
}

// =========================================
// Root namespace tests (namespace = "/")
// =========================================

TEST_F(NodeTopicsExpandTest, root_namespace_relative_path)
{
  auto node_topics = create_node_topics("my_node", "/");
  EXPECT_EQ(node_topics->resolve_topic_name("ping", true), "/ping");
}

TEST_F(NodeTopicsExpandTest, root_namespace_tilde_only)
{
  auto node_topics = create_node_topics("my_node", "/");
  EXPECT_EQ(node_topics->resolve_topic_name("~", true), "/my_node");
}

TEST_F(NodeTopicsExpandTest, root_namespace_tilde_with_topic)
{
  auto node_topics = create_node_topics("my_node", "/");
  EXPECT_EQ(node_topics->resolve_topic_name("~/ping", true), "/my_node/ping");
}

TEST_F(NodeTopicsExpandTest, root_namespace_node_substitution)
{
  auto node_topics = create_node_topics("my_node", "/");
  EXPECT_EQ(node_topics->resolve_topic_name("{node}", true), "/my_node");
}

TEST_F(NodeTopicsExpandTest, root_namespace_ns_substitution)
{
  auto node_topics = create_node_topics("my_node", "/");
  EXPECT_EQ(node_topics->resolve_topic_name("{ns}", true), "/");
}

// =========================================
// Multiple substitutions tests
// =========================================

TEST_F(NodeTopicsExpandTest, multiple_substitutions)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  // {ns} -> "/my_ns", {node} -> "my_node"
  // "{ns}/{node}/topic" -> "/my_ns/my_node/topic"
  EXPECT_EQ(node_topics->resolve_topic_name("{ns}/{node}/topic", true), "/my_ns/my_node/topic");
}

TEST_F(NodeTopicsExpandTest, tilde_with_multiple_substitutions)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  // ~ -> "/my_ns/my_node", {ns} -> "/my_ns", {node} -> "my_node"
  // "~/{ns}/{node}" -> "/my_ns/my_node//my_ns/my_node"
  EXPECT_EQ(
    node_topics->resolve_topic_name("~/{ns}/{node}", true), "/my_ns/my_node//my_ns/my_node");
}

// =========================================
// Error cases
// =========================================

TEST_F(NodeTopicsExpandTest, empty_topic_name_throws)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_THROW(node_topics->resolve_topic_name("", true), std::invalid_argument);
}

TEST_F(NodeTopicsExpandTest, unknown_substitution_throws)
{
  auto node_topics = create_node_topics("my_node", "/my_ns");
  EXPECT_THROW(node_topics->resolve_topic_name("{unknown}", true), std::invalid_argument);
}

// =========================================
// Nested namespace tests
// =========================================

TEST_F(NodeTopicsExpandTest, nested_namespace_relative)
{
  auto node_topics = create_node_topics("my_node", "/ns1/ns2");
  EXPECT_EQ(node_topics->resolve_topic_name("topic", true), "/ns1/ns2/topic");
}

TEST_F(NodeTopicsExpandTest, nested_namespace_tilde)
{
  auto node_topics = create_node_topics("my_node", "/ns1/ns2");
  EXPECT_EQ(node_topics->resolve_topic_name("~/topic", true), "/ns1/ns2/my_node/topic");
}

TEST_F(NodeTopicsExpandTest, nested_namespace_substitution)
{
  auto node_topics = create_node_topics("my_node", "/ns1/ns2");
  // {ns} -> "/ns1/ns2", so "{ns}/topic" -> "/ns1/ns2/topic"
  EXPECT_EQ(node_topics->resolve_topic_name("{ns}/topic", true), "/ns1/ns2/topic");
}

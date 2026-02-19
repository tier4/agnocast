#include "agnocast_kunit_node_name_matching.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node_abc";
static const pid_t PID = 1000;
static const uint32_t QOS_DEPTH = 1;
static const bool QOS_IS_TRANSIENT_LOCAL = false;
static const bool QOS_IS_RELIABLE = true;
static const bool IS_TAKE_SUB = false;
static const bool IGNORE_LOCAL_PUBLICATIONS = false;
static const bool IS_BRIDGE = false;

static void setup_process(struct kunit * test, const pid_t pid)
{
  union ioctl_add_process_args add_process_args;
  int ret = add_process(pid, current->nsproxy->ipc_ns, &add_process_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

// === Subscriber node name tests (covers 1.4: strncmp -> strcmp) ===

void test_case_subscriber_node_exact_match(struct kunit * test)
{
  // Arrange
  setup_process(test, PID);
  union ioctl_add_subscriber_args add_sub_args;
  int ret = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, PID, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL,
    QOS_IS_RELIABLE, IS_TAKE_SUB, IGNORE_LOCAL_PUBLICATIONS, IS_BRIDGE, &add_sub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act & Assert: exact name matches
  KUNIT_EXPECT_EQ(test, count_node_subscriber_topics(current->nsproxy->ipc_ns, NODE_NAME), 1);
}

void test_case_subscriber_node_no_prefix_match(struct kunit * test)
{
  // Arrange: add subscriber with node name "/kunit_test_node_abc"
  setup_process(test, PID);
  union ioctl_add_subscriber_args add_sub_args;
  int ret = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, PID, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL,
    QOS_IS_RELIABLE, IS_TAKE_SUB, IGNORE_LOCAL_PUBLICATIONS, IS_BRIDGE, &add_sub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act & Assert: prefix of the name must NOT match
  KUNIT_EXPECT_EQ(
    test, count_node_subscriber_topics(current->nsproxy->ipc_ns, "/kunit_test_node_ab"), 0);

  // Act & Assert: superstring of the name must NOT match
  KUNIT_EXPECT_EQ(
    test, count_node_subscriber_topics(current->nsproxy->ipc_ns, "/kunit_test_node_abcd"), 0);

  // Act & Assert: different name must NOT match
  KUNIT_EXPECT_EQ(
    test, count_node_subscriber_topics(current->nsproxy->ipc_ns, "/completely_different"), 0);
}

// === Publisher node name tests (covers 1.4: strncmp -> strcmp) ===

void test_case_publisher_node_exact_match(struct kunit * test)
{
  // Arrange
  setup_process(test, PID);
  union ioctl_add_publisher_args add_pub_args;
  int ret = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, PID, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL,
    IS_BRIDGE, &add_pub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act & Assert: exact name matches
  KUNIT_EXPECT_EQ(test, count_node_publisher_topics(current->nsproxy->ipc_ns, NODE_NAME), 1);
}

void test_case_publisher_node_no_prefix_match(struct kunit * test)
{
  // Arrange: add publisher with node name "/kunit_test_node_abc"
  setup_process(test, PID);
  union ioctl_add_publisher_args add_pub_args;
  int ret = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, PID, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL,
    IS_BRIDGE, &add_pub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act & Assert: prefix of the name must NOT match
  KUNIT_EXPECT_EQ(
    test, count_node_publisher_topics(current->nsproxy->ipc_ns, "/kunit_test_node_ab"), 0);

  // Act & Assert: superstring of the name must NOT match
  KUNIT_EXPECT_EQ(
    test, count_node_publisher_topics(current->nsproxy->ipc_ns, "/kunit_test_node_abcd"), 0);

  // Act & Assert: different name must NOT match
  KUNIT_EXPECT_EQ(
    test, count_node_publisher_topics(current->nsproxy->ipc_ns, "/completely_different"), 0);
}

// === get_version test (covers 1.5: memcpy -> strscpy) ===

void test_case_get_version_returns_valid_string(struct kunit * test)
{
  // Arrange
  struct ioctl_get_version_args args;
  memset(&args, 0xFF, sizeof(args));

  // Act
  int ret = get_version_for_test(&args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  // Verify the string is properly NUL-terminated
  KUNIT_EXPECT_LT(test, strlen(args.ret_version), (size_t)VERSION_BUFFER_LEN);
  // Verify the string is non-empty
  KUNIT_EXPECT_GT(test, strlen(args.ret_version), (size_t)0);
}

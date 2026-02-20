#include "agnocast_kunit_node_name_matching.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const char * NODE_NAME_WITH_SUFFIX = "/kunit_test_node_extra";
static const pid_t PID = 1000;
static const uint32_t QOS_DEPTH = 1;
static const bool IS_BRIDGE = false;

static void setup_process(struct kunit * test, const pid_t pid)
{
  union ioctl_add_process_args add_process_args;
  int ret = ioctl_add_process(pid, current->nsproxy->ipc_ns, &add_process_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

void test_case_sub_exact_match(struct kunit * test)
{
  union ioctl_add_subscriber_args add_sub_args;
  int ret;
  int count;

  setup_process(test, PID);

  ret = ioctl_add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, PID, QOS_DEPTH, false, false, false, false,
    IS_BRIDGE, &add_sub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  count = count_node_subscriber_topics(current->nsproxy->ipc_ns, NODE_NAME);
  KUNIT_EXPECT_EQ(test, count, 1);
}

void test_case_sub_prefix_no_match(struct kunit * test)
{
  union ioctl_add_subscriber_args add_sub_args;
  int ret;
  int count;

  setup_process(test, PID);

  ret = ioctl_add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME_WITH_SUFFIX, PID, QOS_DEPTH, false, false,
    false, false, IS_BRIDGE, &add_sub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  count = count_node_subscriber_topics(current->nsproxy->ipc_ns, NODE_NAME);
  KUNIT_EXPECT_EQ_MSG(test, count, 0, "Prefix of node name should not match (strcmp, not strncmp)");
}

void test_case_pub_exact_match(struct kunit * test)
{
  union ioctl_add_publisher_args add_pub_args;
  int ret;
  int count;

  setup_process(test, PID);

  ret = ioctl_add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, PID, QOS_DEPTH, false, IS_BRIDGE,
    &add_pub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  count = count_node_publisher_topics(current->nsproxy->ipc_ns, NODE_NAME);
  KUNIT_EXPECT_EQ(test, count, 1);
}

void test_case_pub_prefix_no_match(struct kunit * test)
{
  union ioctl_add_publisher_args add_pub_args;
  int ret;
  int count;

  setup_process(test, PID);

  ret = ioctl_add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME_WITH_SUFFIX, PID, QOS_DEPTH, false, IS_BRIDGE,
    &add_pub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  count = count_node_publisher_topics(current->nsproxy->ipc_ns, NODE_NAME);
  KUNIT_EXPECT_EQ_MSG(test, count, 0, "Prefix of node name should not match (strcmp, not strncmp)");
}

void test_case_get_version(struct kunit * test)
{
  struct ioctl_get_version_args version_args;
  int ret;

  ret = get_version_for_test(&version_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
  KUNIT_EXPECT_NE(test, version_args.ret_version[0], '\0');
}

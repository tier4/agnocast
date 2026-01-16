#include "agnocast_kunit_get_topic_bridge_exist.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * topic_name = "/kunit_test_topic_bridge";
static const char * node_name = "/kunit_test_node";
static const pid_t publisher_pid = 2000;
static const pid_t subscriber_pid = 1000;
static const uint32_t qos_depth = 1;
static const bool qos_is_transient_local = false;
static const bool qos_is_reliable = false;
static const bool is_take_sub = false;
static const bool ignore_local_publications = false;

void test_case_get_topic_bridge_exist_no_topic(struct kunit * test)
{
  bool ret_pub_exist = true;
  bool ret_sub_exist = true;

  int ret = get_topic_bridge_exist(
    "/non_existent_topic", current->nsproxy->ipc_ns, &ret_pub_exist, &ret_sub_exist);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_FALSE(test, ret_pub_exist);
  KUNIT_EXPECT_FALSE(test, ret_sub_exist);
}

void test_case_get_topic_bridge_exist_normal_nodes(struct kunit * test)
{
  union ioctl_add_publisher_args add_pub_args;
  int ret_add_pub = add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, publisher_pid, qos_depth,
    qos_is_transient_local, false, &add_pub_args);
  KUNIT_ASSERT_EQ(test, ret_add_pub, 0);

  union ioctl_add_subscriber_args add_sub_args;
  int ret_add_sub = add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, subscriber_pid, qos_depth,
    qos_is_transient_local, qos_is_reliable, is_take_sub, ignore_local_publications, false,
    &add_sub_args);
  KUNIT_ASSERT_EQ(test, ret_add_sub, 0);

  bool ret_pub_exist = true;
  bool ret_sub_exist = true;
  int ret =
    get_topic_bridge_exist(topic_name, current->nsproxy->ipc_ns, &ret_pub_exist, &ret_sub_exist);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_FALSE(test, ret_pub_exist);
  KUNIT_EXPECT_FALSE(test, ret_sub_exist);
}

void test_case_get_topic_bridge_exist_publisher_bridge(struct kunit * test)
{
  union ioctl_add_publisher_args add_pub_args;
  int ret_add_pub = add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, publisher_pid, qos_depth,
    qos_is_transient_local, true, &add_pub_args);
  KUNIT_ASSERT_EQ(test, ret_add_pub, 0);

  bool ret_pub_exist = false;
  bool ret_sub_exist = false;
  int ret =
    get_topic_bridge_exist(topic_name, current->nsproxy->ipc_ns, &ret_pub_exist, &ret_sub_exist);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_TRUE(test, ret_pub_exist);
  KUNIT_EXPECT_FALSE(test, ret_sub_exist);
}

void test_case_get_topic_bridge_exist_subscriber_bridge(struct kunit * test)
{
  union ioctl_add_subscriber_args add_sub_args;
  int ret_add_sub = add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, subscriber_pid, qos_depth,
    qos_is_transient_local, qos_is_reliable, is_take_sub, ignore_local_publications, true,
    &add_sub_args);
  KUNIT_ASSERT_EQ(test, ret_add_sub, 0);

  bool ret_pub_exist = false;
  bool ret_sub_exist = false;
  int ret =
    get_topic_bridge_exist(topic_name, current->nsproxy->ipc_ns, &ret_pub_exist, &ret_sub_exist);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_FALSE(test, ret_pub_exist);
  KUNIT_EXPECT_TRUE(test, ret_sub_exist);
}

void test_case_get_topic_bridge_exist_both_bridges(struct kunit * test)
{
  union ioctl_add_publisher_args add_pub_args;
  add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, publisher_pid, qos_depth,
    qos_is_transient_local, true, &add_pub_args);

  union ioctl_add_subscriber_args add_sub_args;
  add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, subscriber_pid, qos_depth,
    qos_is_transient_local, qos_is_reliable, is_take_sub, ignore_local_publications, true,
    &add_sub_args);

  bool ret_pub_exist = false;
  bool ret_sub_exist = false;
  int ret =
    get_topic_bridge_exist(topic_name, current->nsproxy->ipc_ns, &ret_pub_exist, &ret_sub_exist);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_TRUE(test, ret_pub_exist);
  KUNIT_EXPECT_TRUE(test, ret_sub_exist);
}

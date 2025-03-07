#include "agnocast_kunit_publisher_add.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * topic_name = "/kunit_test_topic";
static const char * node_name = "/kunit_test_node";
static const pid_t publisher_pid = 1000;
static const uint32_t qos_depth = 1;
static const bool qos_is_transient_local = false;

void test_case_publisher_add_normal(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, get_publisher_num(topic_name), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);

  union ioctl_publisher_args publisher_args;
  int ret = publisher_add(
    topic_name, node_name, publisher_pid, qos_depth, qos_is_transient_local, &publisher_args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(topic_name), 1);
  KUNIT_EXPECT_EQ(test, publisher_args.ret_id, 0);
  KUNIT_EXPECT_TRUE(test, is_in_publisher_htable(topic_name, publisher_args.ret_id));
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

void test_case_publisher_add_many(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, get_publisher_num(topic_name), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);

  const int publisher_num = MAX_PUBLISHER_NUM;
  int ret;
  union ioctl_publisher_args publisher_args;
  for (int i = 0; i < publisher_num; i++) {
    ret = publisher_add(
      topic_name, node_name, publisher_pid, qos_depth, qos_is_transient_local, &publisher_args);
  }

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, publisher_args.ret_id, publisher_num - 1);
  KUNIT_EXPECT_EQ(test, get_publisher_num(topic_name), publisher_num);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

void test_case_publisher_add_too_many(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, get_publisher_num(topic_name), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);

  const int publisher_num = MAX_PUBLISHER_NUM + 1;
  int ret = 0;
  for (int i = 0; i < publisher_num; i++) {
    union ioctl_publisher_args publisher_args;
    ret = publisher_add(
      topic_name, node_name, publisher_pid, qos_depth, qos_is_transient_local, &publisher_args);
  }

  KUNIT_EXPECT_EQ(test, ret, -ENOBUFS);
  KUNIT_EXPECT_EQ(test, get_publisher_num(topic_name), MAX_PUBLISHER_NUM);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

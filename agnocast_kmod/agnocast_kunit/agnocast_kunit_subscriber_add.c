#include "agnocast_kunit_subscriber_add.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const bool QOS_IS_TRANSIENT_LOCAL = false;
static const bool IS_TAKE_SUB = false;

static void setup_process(struct kunit * test, const pid_t pid)
{
  union ioctl_new_shm_args new_shm_args;
  int ret = new_shm_addr(pid, PAGE_SIZE, &new_shm_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

void test_case_subscriber_add_normal(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const pid_t subscriber_pid = 1000;
  const uint32_t qos_depth = 1;
  setup_process(test, subscriber_pid);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid));

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 0);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
}

void test_case_subscriber_add_invalid_qos(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const pid_t subscriber_pid = 1000;
  const uint32_t invalid_qos_depth = MAX_QOS_DEPTH + 1;
  setup_process(test, subscriber_pid);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, invalid_qos_depth, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_subscriber_add_too_many_subscribers(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const pid_t subscriber_pid = 1000;
  setup_process(test, subscriber_pid);
  for (uint32_t i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    union ioctl_subscriber_args subscriber_args;
    subscriber_add(
      TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
      &subscriber_args);
  }

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ENOBUFS);
}

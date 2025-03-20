#include "agnocast_kunit_decrement_rc.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const bool QOS_IS_TRANSIENT_LOCAL = true;
static const uint32_t QOS_DEPTH = 1;
static pid_t publisher_pid = 2000;

static void setup_one_publisher(
  struct kunit * test, topic_local_id_t * ret_publisher_id, uint64_t * ret_addr)
{
  publisher_pid++;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  *ret_addr = new_shm_args.ret_addr;
  *ret_publisher_id = publisher_args.ret_id;
}

void test_case_decrement_rc_no_topic(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, decrement_message_entry_rc(TOPIC_NAME, 0, 0), -EINVAL);
}

void test_case_decrement_rc_no_message(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_topic_num(), 0);

  // Arrange
  topic_local_id_t ret_publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, &ret_publisher_id, &ret_addr);

  // Act
  int ret = decrement_message_entry_rc(TOPIC_NAME, ret_publisher_id, 0);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_decrement_rc_last_reference(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_topic_num(), 0);

  // Arrange
  topic_local_id_t ret_publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, &ret_publisher_id, &ret_addr);

  union ioctl_publish_args publish_args;
  int ret = publish_msg(TOPIC_NAME, ret_publisher_id, ret_addr, &publish_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act
  int ret_sut = decrement_message_entry_rc(TOPIC_NAME, ret_publisher_id, publish_args.ret_entry_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret_sut, 0);
  KUNIT_EXPECT_EQ(test, get_entry_rc(TOPIC_NAME, publish_args.ret_entry_id, ret_publisher_id), 0);
}

void test_case_decrement_rc_multi_reference(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_topic_num(), 0);

  // Arrange
  topic_local_id_t ret_publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, &ret_publisher_id, &ret_addr);

  union ioctl_publish_args publish_args;
  int ret1 = publish_msg(TOPIC_NAME, ret_publisher_id, ret_addr, &publish_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  const pid_t subscriber_pid = 1000;
  union ioctl_new_shm_args new_shm_args;
  int ret2 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_subscriber_args subscriber_args;
  int ret3 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, false,
    &subscriber_args);

  KUNIT_ASSERT_EQ(test, subscriber_args.ret_transient_local_num, 1);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  int ret4 = increment_message_entry_rc(
    TOPIC_NAME, subscriber_args.ret_id, subscriber_args.ret_entry_ids[0]);
  KUNIT_ASSERT_EQ(test, ret4, 0);

  // Act
  int ret_sut = decrement_message_entry_rc(
    TOPIC_NAME, subscriber_args.ret_id, subscriber_args.ret_entry_ids[0]);

  // Assert
  KUNIT_EXPECT_EQ(test, ret_sut, 0);
  KUNIT_EXPECT_EQ(test, get_entry_rc(TOPIC_NAME, publish_args.ret_entry_id, ret_publisher_id), 1);
}

#include "agnocast_kunit_take_msg.h"

#include "../agnocast.h"

#include <kunit/test.h>

static char * TOPIC_NAME = "/kunit_test_topic";
static char * NODE_NAME = "/kunit_test_node";
static bool IS_TAKE_SUB = true;

static void setup_one_subscriber(
  struct kunit * test, pid_t subscriber_pid, uint32_t qos_depth, bool is_transient_local,
  topic_local_id_t * subscriber_id)
{
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, is_transient_local, IS_TAKE_SUB,
    &subscriber_args);
  *subscriber_id = subscriber_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_publisher(
  struct kunit * test, pid_t publisher_pid, uint32_t qos_depth, bool is_transient_local,
  topic_local_id_t * publisher_id, uint64_t * ret_addr)
{
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  *ret_addr = new_shm_args.ret_addr;

  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, qos_depth, is_transient_local, &publisher_args);
  *publisher_id = publisher_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

void test_case_take_msg_no_topic(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id = 0;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  bool is_transient_local = true;

  // Act
  int ret = take_msg(TOPIC_NAME, subscriber_id, is_transient_local, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_take_msg_no_subscriber(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool publisher_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  topic_local_id_t subscriber_id = 0;
  bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret = take_msg(TOPIC_NAME, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_take_msg_no_publish_nothing_to_take(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret = take_msg(TOPIC_NAME, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_take_one(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(TOPIC_NAME, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id), ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_take_the_second_one_when_sub_qos_depth_is_two(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  union ioctl_publish_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret3 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret1.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id), ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_take_one_again_with_allow_same_message(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret1;
  int ret2 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_ASSERT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id),
    ioctl_take_msg_ret1.ret_entry_id);

  union ioctl_take_msg_args ioctl_take_msg_ret2;

  // Act
  int ret3 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret2);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id),
    ioctl_take_msg_ret1.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_take_one_again_not_allow_same_message(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret1;
  int ret2 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_ASSERT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id),
    ioctl_take_msg_ret1.ret_entry_id);

  union ioctl_take_msg_args ioctl_take_msg_ret2;

  // Act
  int ret3 = take_msg(TOPIC_NAME, subscriber_id, false, &ioctl_take_msg_ret2);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_entry_id, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_sub_qos_depth_smaller_than_publish_num_smaller_than_pub_qos_depth(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  union ioctl_publish_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(TOPIC_NAME, publisher_id, ret_addr + 1, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret3 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret2.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id), ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_publish_num_smaller_than_sub_qos_depth_smaller_than_pub_qos_depth(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 2;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id), ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_sub_qos_depth_smaller_than_pub_qos_depth_smaller_than_publish_num(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = MAX_QOS_DEPTH;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  for (int i = 0; i < MAX_QOS_DEPTH; i++) {
    union ioctl_publish_args ioctl_publish_msg_ret;
    int ret = publish_msg(TOPIC_NAME, publisher_id, ret_addr + i, &ioctl_publish_msg_ret);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 =
    publish_msg(TOPIC_NAME, publisher_id, ret_addr + MAX_QOS_DEPTH + 1, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id), ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_publish_num_and_sub_qos_depth_and_pub_qos_depth_are_all_max_qos_depth(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = MAX_QOS_DEPTH;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = MAX_QOS_DEPTH;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret, 0);

  for (int i = 0; i < MAX_QOS_DEPTH - 1; i++) {
    union ioctl_publish_args ioctl_publish_msg_ret;
    int ret = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret3 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, subscriber_id),
    ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_too_many_rc(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = MAX_QOS_DEPTH;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(TOPIC_NAME, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    int ret = increment_message_entry_rc(
      TOPIC_NAME, subscriber_id + i + 1, ioctl_publish_msg_ret1.ret_entry_id);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, -ENOBUFS);
}

// ================================================
// Tests for set_publisher_shm_info

void test_case_take_msg_one_new_pub(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 10;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool is_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
}

void test_case_take_msg_pubsub_in_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_new_shm_args new_shm_args;
  const pid_t pid = 1000;
  int ret1 = new_shm_addr(pid, PAGE_SIZE, &new_shm_args);
  const bool is_transient_local = true;

  union ioctl_subscriber_args subscriber_args;
  const uint32_t subscriber_qos_depth = 10;
  int ret2 = subscriber_add(
    TOPIC_NAME, NODE_NAME, pid, subscriber_qos_depth, is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  union ioctl_publisher_args publisher_args;
  const uint32_t publisher_qos_depth = 10;
  int ret3 = publisher_add(
    TOPIC_NAME, NODE_NAME, pid, publisher_qos_depth, is_transient_local, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(TOPIC_NAME, subscriber_args.ret_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_2pub_in_same_process(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 10;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_new_shm_args new_shm_args;
  const pid_t publisher_pid = 1000;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);

  union ioctl_publisher_args publisher_args1;
  const uint32_t publisher_qos_depth1 = 10;
  const bool is_transient_local1 = true;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, publisher_qos_depth1, is_transient_local1,
    &publisher_args1);

  union ioctl_publisher_args publisher_args2;
  const uint32_t publisher_qos_depth2 = 1;
  const bool is_transient_local2 = true;
  int ret3 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, publisher_qos_depth2, is_transient_local2,
    &publisher_args2);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(TOPIC_NAME, subscriber_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
}

void test_case_take_msg_2sub_in_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_new_shm_args new_shm_args;
  const pid_t subscriber_pid = 2000;
  int ret1 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);
  const bool is_transient_local = true;

  union ioctl_subscriber_args subscriber_args1;
  const uint32_t subscriber_qos_depth1 = 10;
  int ret2 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, subscriber_qos_depth1, is_transient_local, IS_TAKE_SUB,
    &subscriber_args1);

  union ioctl_subscriber_args subscriber_args2;
  const uint32_t subscriber_qos_depth2 = 1;
  int ret3 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, subscriber_qos_depth2, is_transient_local, IS_TAKE_SUB,
    &subscriber_args2);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);

  union ioctl_take_msg_args ioctl_take_msg_ret;
  int ret4 = take_msg(TOPIC_NAME, subscriber_args1.ret_id, true, &ioctl_take_msg_ret);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);

  // Act
  int ret5 = take_msg(TOPIC_NAME, subscriber_args2.ret_id, true, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret5, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_too_many_mapping_processes(struct kunit * test)
{
  // TODO(Koichi98): Implement this test case
  KUNIT_EXPECT_EQ(test, 0, 0);
}
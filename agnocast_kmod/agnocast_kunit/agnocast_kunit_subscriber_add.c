#include "agnocast_kunit_subscriber_add.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const bool IS_TAKE_SUB = false;

// ================================================
// helper functions for subscriber_add test

static void setup_process(struct kunit * test, const pid_t pid)
{
  union ioctl_new_shm_args new_shm_args;
  int ret = new_shm_addr(pid, PAGE_SIZE, &new_shm_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

static void setup_subscriber(struct kunit * test, const pid_t pid)
{
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = true;
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB, &subscriber_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

static void setup_publisher(struct kunit * test, const pid_t pid)
{
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = true;
  union ioctl_publisher_args publisher_args;
  int ret =
    publisher_add(TOPIC_NAME, NODE_NAME, pid, qos_depth, qos_is_transient_local, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

static void setup_entry(struct kunit * test, const pid_t pid)
{
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = true;
  union ioctl_publisher_args publisher_args;
  int ret1 =
    publisher_add(TOPIC_NAME, NODE_NAME, pid, qos_depth, qos_is_transient_local, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_publish_args publish_args;
  int ret2 = publish_msg(TOPIC_NAME, publisher_args.ret_id, 0, &publish_args);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  int ret3 =
    decrement_message_entry_rc(TOPIC_NAME, publisher_args.ret_id, publish_args.ret_entry_id);
  KUNIT_ASSERT_EQ(test, ret3, 0);
}

static void setup_many_entries(
  struct kunit * test, const pid_t pid, const uint32_t publisher_qos_depth, const uint32_t num)
{
  const bool qos_is_transient_local = true;
  union ioctl_publisher_args publisher_args;
  int ret1 = publisher_add(
    TOPIC_NAME, NODE_NAME, pid, publisher_qos_depth, qos_is_transient_local, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  for (uint32_t i = 0; i < num; i++) {
    union ioctl_publish_args publish_args;
    int ret2 = publish_msg(TOPIC_NAME, publisher_args.ret_id, PAGE_SIZE * i, &publish_args);
    KUNIT_ASSERT_EQ(test, ret2, 0);

    int ret3 =
      decrement_message_entry_rc(TOPIC_NAME, publisher_args.ret_id, publish_args.ret_entry_id);
    KUNIT_ASSERT_EQ(test, ret3, 0);
  }
}

// ================================================
// test cases

void test_case_subscriber_add_normal(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const pid_t subscriber_pid = 1000;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  setup_process(test, subscriber_pid);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid));

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 0);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
}

void test_case_subscriber_add_normal_with_publisher(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_publisher(test, publisher_pid);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
}

void test_case_subscriber_add_normal_with_publisher_of_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  const pid_t pid = 1000;
  setup_process(test, pid);
  setup_publisher(test, pid);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB, &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 0);
}

void test_case_subscriber_add_normal_with_subscriber_of_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  setup_process(test, publisher_pid);
  setup_process(test, subscriber_pid);
  setup_publisher(test, publisher_pid);
  setup_subscriber(test, subscriber_pid);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 0);
}

void test_case_subscriber_add_normal_with_many_publishers_of_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  setup_process(test, publisher_pid);
  setup_process(test, subscriber_pid);
  for (uint32_t i = 0; i < MAX_PUBLISHER_NUM; i++) {
    setup_publisher(test, publisher_pid);
  }

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
}

void test_case_subscriber_add_normal_with_entry(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = true;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_entry(test, publisher_pid);
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), 1);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_entry_ids[0], 0);
}

// publisher_qos_depth > entries_num > subscriber_qos_depth
void test_case_subscriber_add_normal_with_many_entries1(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const bool qos_is_transient_local = true;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  const uint32_t publisher_qos_depth = 7;
  const uint32_t subscriber_qos_depth = 3;
  const uint32_t entries_num = 5;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_many_entries(test, publisher_pid, publisher_qos_depth, entries_num);
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), entries_num);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, subscriber_qos_depth, qos_is_transient_local,
    IS_TAKE_SUB, &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, subscriber_qos_depth);
  for (uint32_t i = 1; i < subscriber_qos_depth; i++) {
    KUNIT_EXPECT_TRUE(
      test, subscriber_args.ret_entry_ids[i - 1] > subscriber_args.ret_entry_ids[i]);
  }
}

// publisher_qos_depth > subscriber_qos_depth > entries_num
void test_case_subscriber_add_normal_with_many_entries2(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const bool qos_is_transient_local = true;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  const uint32_t publisher_qos_depth = 7;
  const uint32_t subscriber_qos_depth = 5;
  const uint32_t entries_num = 3;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_many_entries(test, publisher_pid, publisher_qos_depth, entries_num);
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), entries_num);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, subscriber_qos_depth, qos_is_transient_local,
    IS_TAKE_SUB, &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, entries_num);
  for (uint32_t i = 1; i < entries_num; i++) {
    KUNIT_EXPECT_TRUE(
      test, subscriber_args.ret_entry_ids[i - 1] > subscriber_args.ret_entry_ids[i]);
  }
}

// entries_num > publisher_qos_depth > subscriber_qos_depth
void test_case_subscriber_add_normal_with_many_entries3(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const bool qos_is_transient_local = true;
  const pid_t publisher_pid = 999;
  const pid_t subscriber_pid = 1000;
  const uint32_t publisher_qos_depth = 5;
  const uint32_t subscriber_qos_depth = 3;
  const uint32_t entries_num = 7;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_many_entries(test, publisher_pid, publisher_qos_depth, entries_num);
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), publisher_qos_depth);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, subscriber_qos_depth, qos_is_transient_local,
    IS_TAKE_SUB, &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, subscriber_qos_depth);
  for (uint32_t i = 1; i < subscriber_qos_depth; i++) {
    KUNIT_EXPECT_TRUE(
      test, subscriber_args.ret_entry_ids[i - 1] > subscriber_args.ret_entry_ids[i]);
  }
}

void test_case_subscriber_add_invalid_qos(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const pid_t subscriber_pid = 1000;
  const bool qos_is_transient_local = false;
  const uint32_t invalid_qos_depth = MAX_QOS_DEPTH + 1;
  setup_process(test, subscriber_pid);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, invalid_qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_subscriber_add_too_many_subscribers(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  const pid_t subscriber_pid = 1000;
  setup_process(test, subscriber_pid);
  for (uint32_t i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    union ioctl_subscriber_args subscriber_args;
    subscriber_add(
      TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
      &subscriber_args);
  }

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ENOBUFS);
}

void test_case_subscriber_add_without_self_process(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const pid_t subscriber_pid = 1000;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ESRCH);
}

void test_case_subscriber_add_without_publisher_process(struct kunit * test)
{
  // Arrange
  union ioctl_subscriber_args subscriber_args;
  const pid_t subscriber_pid = 1000;
  const uint32_t qos_depth = 1;
  const bool qos_is_transient_local = false;
  setup_process(test, subscriber_pid);
  const pid_t publisher_pid = subscriber_pid - 1;
  setup_publisher(test, publisher_pid);
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);

  // Act
  int ret = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, qos_depth, qos_is_transient_local, IS_TAKE_SUB,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ESRCH);
}

void test_case_subscriber_add_too_many_mmap(struct kunit * test)
{
  // TODO(Ryuta Kambe): Implement this test case
  KUNIT_EXPECT_EQ(test, 0, 0);
}

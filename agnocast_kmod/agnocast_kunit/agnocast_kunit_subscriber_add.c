#include "agnocast_kunit_subscriber_add.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

#include <kunit/test.h>

static const char * topic_name = "/kunit_test_topic";
static const char * node_name = "/kunit_test_node";
static const pid_t subscriber_pid = 1000;
static const uint32_t qos_depth = 1;
static const bool qos_is_transient_local = false;
static const bool is_take_sub = false;

// ================================================
// helper functions for subscriber_add test

static void setup_process(struct kunit * test, const pid_t pid)
{
  union ioctl_new_shm_args new_shm_args;
  int ret = new_shm_addr(pid, PAGE_SIZE, &new_shm_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

static void setup_publisher(struct kunit * test, const pid_t pid)
{
  union ioctl_publisher_args publisher_args;
  int ret =
    publisher_add(topic_name, node_name, pid, qos_depth, qos_is_transient_local, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
}

static void setup_entry(struct kunit * test, const pid_t pid)
{
  union ioctl_publisher_args publisher_args;
  int ret1 = publisher_add(topic_name, node_name, pid, qos_depth, true, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_publish_args publish_args;
  int ret2 = publish_msg(topic_name, publisher_args.ret_id, 0, &publish_args);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  int ret3 =
    decrement_message_entry_rc(topic_name, publisher_args.ret_id, publish_args.ret_entry_id);
  KUNIT_ASSERT_EQ(test, ret3, 0);
}

static void setup_many_entries(
  struct kunit * test, const pid_t pid, const uint32_t publisher_qos_depth, const uint32_t num)
{
  union ioctl_publisher_args publisher_args;
  int ret1 = publisher_add(topic_name, node_name, pid, publisher_qos_depth, true, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  for (uint32_t i = 0; i < num; i++) {
    union ioctl_publish_args publish_args;
    int ret2 = publish_msg(topic_name, publisher_args.ret_id, PAGE_SIZE * i, &publish_args);
    KUNIT_ASSERT_EQ(test, ret2, 0);

    int ret3 =
      decrement_message_entry_rc(topic_name, publisher_args.ret_id, publish_args.ret_entry_id);
    KUNIT_ASSERT_EQ(test, ret3, 0);
  }
}

// ================================================
// test cases

void test_case_subscriber_add_normal(struct kunit * test)
{
  // Arrang
  setup_process(test, subscriber_pid);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid));

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(topic_name, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 0);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(topic_name, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

void test_case_subscriber_add_normal_with_publisher(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = subscriber_pid - 1;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_publisher(test, publisher_pid);

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(topic_name, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 1);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(topic_name, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

void test_case_subscriber_add_normal_with_entry(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = subscriber_pid - 1;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_entry(test, publisher_pid);
  KUNIT_ASSERT_EQ(test, get_publisher_num(topic_name), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(topic_name), 1);

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, true, is_take_sub, &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(topic_name, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 1);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(topic_name, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_entry_ids[0], 0);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

// publisher_qos_depth > entries_num > subscriber_qos_depth
void test_case_subscriber_add_normal_with_many_entries1(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = subscriber_pid - 1;
  const uint32_t publisher_qos_depth = 7;
  const uint32_t subscriber_qos_depth = 3;
  const uint32_t entries_num = 5;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_many_entries(test, publisher_pid, publisher_qos_depth, entries_num);
  KUNIT_ASSERT_EQ(test, get_publisher_num(topic_name), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(topic_name), entries_num);

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, subscriber_qos_depth, true, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(topic_name, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 1);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(topic_name, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, subscriber_qos_depth);
  for (uint32_t i = 1; i < subscriber_qos_depth; i++) {
    KUNIT_EXPECT_TRUE(
      test, subscriber_args.ret_entry_ids[i - 1] > subscriber_args.ret_entry_ids[i]);
  }
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

// publisher_qos_depth > subscriber_qos_depth > entries_num
void test_case_subscriber_add_normal_with_many_entries2(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = subscriber_pid - 1;
  const uint32_t publisher_qos_depth = 7;
  const uint32_t subscriber_qos_depth = 5;
  const uint32_t entries_num = 3;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_many_entries(test, publisher_pid, publisher_qos_depth, entries_num);
  KUNIT_ASSERT_EQ(test, get_publisher_num(topic_name), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(topic_name), entries_num);

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, subscriber_qos_depth, true, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(topic_name, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 1);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(topic_name, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, entries_num);
  for (uint32_t i = 1; i < entries_num; i++) {
    KUNIT_EXPECT_TRUE(
      test, subscriber_args.ret_entry_ids[i - 1] > subscriber_args.ret_entry_ids[i]);
  }
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

// entries_num > publisher_qos_depth > subscriber_qos_depth
void test_case_subscriber_add_normal_with_many_entries3(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = subscriber_pid - 1;
  const uint32_t publisher_qos_depth = 5;
  const uint32_t subscriber_qos_depth = 3;
  const uint32_t entries_num = 7;
  setup_process(test, subscriber_pid);
  setup_process(test, publisher_pid);
  setup_many_entries(test, publisher_pid, publisher_qos_depth, entries_num);
  KUNIT_ASSERT_EQ(test, get_publisher_num(topic_name), 1);
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(topic_name), publisher_qos_depth);

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, subscriber_qos_depth, true, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  get_subscriber_num(topic_name, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_id, 1);
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(topic_name, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_transient_local_num, subscriber_qos_depth);
  for (uint32_t i = 1; i < subscriber_qos_depth; i++) {
    KUNIT_EXPECT_TRUE(
      test, subscriber_args.ret_entry_ids[i - 1] > subscriber_args.ret_entry_ids[i]);
  }
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_args.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(topic_name));
}

void test_case_subscriber_add_invalid_qos(struct kunit * test)
{
  // Arrange
  setup_process(test, subscriber_pid);

  // Act
  const uint32_t invalid_qos_depth = MAX_QOS_DEPTH + 1;
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, invalid_qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_subscriber_add_too_many_subscribers(struct kunit * test)
{
  // Arrange
  setup_process(test, subscriber_pid);
  for (uint32_t i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    union ioctl_subscriber_args subscriber_args;
    subscriber_add(
      topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
      &subscriber_args);
  }

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ENOBUFS);
}

void test_case_subscriber_add_without_self_process(struct kunit * test)
{
  // Arrange

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ESRCH);
}

void test_case_subscriber_add_without_publisher_process(struct kunit * test)
{
  // Arrange
  setup_process(test, subscriber_pid);
  const pid_t publisher_pid = subscriber_pid - 1;
  setup_publisher(test, publisher_pid);
  KUNIT_ASSERT_EQ(test, get_publisher_num(topic_name), 1);

  // Act
  union ioctl_subscriber_args subscriber_args;
  int ret = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ESRCH);
}

void test_case_subscriber_add_too_many_mmap(struct kunit * test)
{
  // TODO(Ryuta Kambe): Implement this test case
  KUNIT_EXPECT_EQ(test, 0, 0);
}

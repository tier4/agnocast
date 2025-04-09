#include "agnocast_kunit_take_msg.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

#include <kunit/test.h>
#include <linux/delay.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const bool IS_TAKE_SUB = true;

static void setup_one_subscriber(
  struct kunit * test, pid_t subscriber_pid, uint32_t qos_depth, bool is_transient_local,
  topic_local_id_t * subscriber_id)
{
  union ioctl_get_new_shm_args get_new_shm_args;
  int ret1 = get_new_shm_addr(subscriber_pid, PAGE_SIZE, &get_new_shm_args);

  union ioctl_add_subscriber_args add_subscriber_args;
  int ret2 = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid, qos_depth, is_transient_local,
    IS_TAKE_SUB, &add_subscriber_args);
  *subscriber_id = add_subscriber_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_publisher(
  struct kunit * test, pid_t publisher_pid, uint32_t qos_depth, bool is_transient_local,
  topic_local_id_t * publisher_id, uint64_t * ret_addr)
{
  union ioctl_get_new_shm_args get_new_shm_args;
  int ret1 = get_new_shm_addr(publisher_pid, PAGE_SIZE, &get_new_shm_args);
  *ret_addr = get_new_shm_args.ret_addr;

  union ioctl_add_publisher_args add_publisher_args;
  int ret2 = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, qos_depth, is_transient_local,
    &add_publisher_args);
  *publisher_id = add_publisher_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

void test_case_take_msg_no_topic(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id = 0;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  bool is_transient_local = false;

  // Act
  int ret = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, is_transient_local, &ioctl_take_msg_ret);

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
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  topic_local_id_t subscriber_id = 0;
  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_take_msg_no_publish_nothing_to_take(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_take_one(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool is_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, is_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_take_the_first_one_when_sub_qos_depth_is_two(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 2;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  union ioctl_publish_msg_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret3 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret1.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_take_one_again_with_allow_same_message(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret1;
  const bool allow_same_message = true;
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_ASSERT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret1.ret_entry_id);

  union ioctl_take_msg_args ioctl_take_msg_ret2;

  // Act
  int ret3 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret2);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret1.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_take_one_again_not_allow_same_message(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_take_msg_args ioctl_take_msg_ret1;
  const bool allow_same_message = false;
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_ASSERT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret1.ret_entry_id);

  union ioctl_take_msg_args ioctl_take_msg_ret2;

  // Act
  int ret3 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret2);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_addr, 0);
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
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  union ioctl_publish_msg_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr + 1, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret3 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret2.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_publish_num_smaller_than_sub_qos_depth_smaller_than_pub_qos_depth(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 2;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_sub_qos_depth_smaller_than_pub_qos_depth_smaller_than_publish_num(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = MAX_QOS_DEPTH;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  for (int i = 0; i < MAX_QOS_DEPTH; i++) {
    union ioctl_publish_msg_args ioctl_publish_msg_ret;
    int ret = publish_msg(
      TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr + i, &ioctl_publish_msg_ret);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }
  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr + MAX_QOS_DEPTH + 1,
    &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_publish_num_and_sub_qos_depth_and_pub_qos_depth_are_all_max_qos_depth(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = MAX_QOS_DEPTH;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = MAX_QOS_DEPTH;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret, 0);

  for (int i = 0; i < MAX_QOS_DEPTH - 1; i++) {
    union ioctl_publish_msg_args ioctl_publish_msg_ret;
    int ret = publish_msg(
      TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret3 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_transient_local_sub_qos_and_pub_qos_and_publish_num_are_all_equal(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 1;
  const bool publisher_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_transient_local_sub_qos_smaller_than_pub_qos_smaller_than_publish_num(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 2;
  const bool publisher_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  union ioctl_publish_msg_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_publish_msg_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr + 1, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  union ioctl_publish_msg_args ioctl_publish_msg_ret3;
  int ret3 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret3);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret3.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

//
void test_case_take_msg_transient_local_sub_qos_smaller_than_publish_num_smaller_than_pub_qos(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool publisher_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  union ioctl_publish_msg_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_publish_msg_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr + 1, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 1;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret2.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_transient_local_publish_num_smaller_than_sub_qos_smaller_than_pub_qos(
  struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool publisher_transient_local = true;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  union ioctl_publish_msg_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_publish_msg_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, ret_addr + 1, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 3;
  const bool subscriber_transient_local = true;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_entry_id, ioctl_publish_msg_ret1.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id),
    ioctl_take_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

// ================================================
// Tests for set_publisher_shm_info

void test_case_take_msg_one_new_pub(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 10;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  const uint32_t publisher_qos_depth = 10;
  const bool publisher_transient_local = false;
  setup_one_publisher(
    test, publisher_pid, publisher_qos_depth, publisher_transient_local, &publisher_id, &ret_addr);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);
}

void test_case_take_msg_pubsub_in_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_get_new_shm_args get_new_shm_args;
  const pid_t pid = 1000;
  int ret1 = get_new_shm_addr(pid, PAGE_SIZE, &get_new_shm_args);
  const bool publisher_transient_local = false;

  union ioctl_add_subscriber_args add_subscriber_args;
  const uint32_t subscriber_qos_depth = 10;
  int ret2 = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, pid, subscriber_qos_depth,
    publisher_transient_local, IS_TAKE_SUB, &add_subscriber_args);

  union ioctl_add_publisher_args add_publisher_args;
  const uint32_t publisher_qos_depth = 10;
  int ret3 = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, pid, publisher_qos_depth,
    publisher_transient_local, &add_publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, add_subscriber_args.ret_id, allow_same_message,
    &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_2pub_in_same_process(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  const pid_t subscriber_pid = 2000;
  const uint32_t subscriber_qos_depth = 10;
  const bool subscriber_transient_local = false;
  setup_one_subscriber(
    test, subscriber_pid, subscriber_qos_depth, subscriber_transient_local, &subscriber_id);

  union ioctl_get_new_shm_args get_new_shm_args;
  const pid_t publisher_pid = 1000;
  int ret1 = get_new_shm_addr(publisher_pid, PAGE_SIZE, &get_new_shm_args);

  union ioctl_add_publisher_args add_publisher_args1;
  const uint32_t publisher_qos_depth1 = 10;
  const bool publisher_transient_local1 = true;
  int ret2 = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, publisher_qos_depth1,
    publisher_transient_local1, &add_publisher_args1);

  union ioctl_add_publisher_args add_publisher_args2;
  const uint32_t publisher_qos_depth2 = 1;
  const bool publisher_transient_local2 = true;
  int ret3 = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, publisher_qos_depth2,
    publisher_transient_local2, &add_publisher_args2);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  const bool allow_same_message = true;
  union ioctl_take_msg_args ioctl_take_msg_ret;

  // Act
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, allow_same_message, &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], get_new_shm_args.ret_addr);
}

void test_case_take_msg_2sub_in_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_get_new_shm_args get_new_shm_args;
  const pid_t subscriber_pid = 2000;
  int ret1 = get_new_shm_addr(subscriber_pid, PAGE_SIZE, &get_new_shm_args);
  const bool is_transient_local = false;

  union ioctl_add_subscriber_args add_subscriber_args1;
  const uint32_t subscriber_qos_depth1 = 10;
  int ret2 = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid, subscriber_qos_depth1,
    is_transient_local, IS_TAKE_SUB, &add_subscriber_args1);

  union ioctl_add_subscriber_args add_subscriber_args2;
  const uint32_t subscriber_qos_depth2 = 1;
  int ret3 = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid, subscriber_qos_depth2,
    is_transient_local, IS_TAKE_SUB, &add_subscriber_args2);
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
  const bool allow_same_message = true;
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, add_subscriber_args1.ret_id, allow_same_message,
    &ioctl_take_msg_ret);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.shm_addrs[0], ret_addr);

  // Act
  int ret5 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, add_subscriber_args2.ret_id, allow_same_message,
    &ioctl_take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret5, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_with_exited_publisher(struct kunit * test)
{
  // Arrange
  const uint32_t qos_depth = 1;
  const bool is_transient_local = true;
  const bool allow_same_message = true;

  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  const pid_t publisher_pid = 1000;
  setup_one_publisher(test, publisher_pid, qos_depth, is_transient_local, &publisher_id, &ret_addr);

  uint64_t msg_addr = 0x1000;
  union ioctl_publish_msg_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, msg_addr, &ioctl_publish_msg_ret);

  topic_local_id_t subscriber_id1;
  const pid_t subscriber_pid1 = 2000;
  setup_one_subscriber(test, subscriber_pid1, qos_depth, is_transient_local, &subscriber_id1);

  union ioctl_take_msg_args ioctl_take_msg_ret1;
  int ret2 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id1, allow_same_message, &ioctl_take_msg_ret1);

  enqueue_exit_pid(publisher_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  topic_local_id_t subscriber_id2;
  const pid_t subscriber_pid2 = 2001;
  setup_one_subscriber(test, subscriber_pid2, qos_depth, is_transient_local, &subscriber_id2);

  union ioctl_get_subscriber_num_args ioctl_get_subscriber_num_ret;
  int ret3 =
    get_subscriber_num(TOPIC_NAME, current->nsproxy->ipc_ns, &ioctl_get_subscriber_num_ret);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 2);
  KUNIT_ASSERT_FALSE(test, is_in_proc_info_htable(publisher_pid));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid2));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME, current->nsproxy->ipc_ns), 1);
  KUNIT_ASSERT_TRUE(
    test, is_in_publisher_htable(TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id));
  KUNIT_ASSERT_EQ(test, ioctl_get_subscriber_num_ret.ret_subscriber_num, 2);
  KUNIT_ASSERT_TRUE(
    test, is_in_subscriber_htable(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id1));
  KUNIT_ASSERT_TRUE(
    test, is_in_subscriber_htable(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id2));
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME, current->nsproxy->ipc_ns), 1);
  KUNIT_ASSERT_EQ(
    test,
    get_entry_rc(
      TOPIC_NAME, current->nsproxy->ipc_ns, ioctl_publish_msg_ret.ret_entry_id, publisher_id),
    0);
  KUNIT_ASSERT_EQ(
    test,
    get_entry_rc(
      TOPIC_NAME, current->nsproxy->ipc_ns, ioctl_publish_msg_ret.ret_entry_id, subscriber_id1),
    1);
  KUNIT_ASSERT_EQ(
    test,
    get_entry_rc(
      TOPIC_NAME, current->nsproxy->ipc_ns, ioctl_publish_msg_ret.ret_entry_id, subscriber_id2),
    0);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_entry_id, ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_addr, msg_addr);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.publisher_num, 1);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.publisher_pids[0], publisher_pid);
  KUNIT_ASSERT_EQ(test, ioctl_take_msg_ret1.ret_pub_shm_info.shm_addrs[0], ret_addr);

  // Act
  union ioctl_take_msg_args ioctl_take_msg_ret2;
  int ret4 = take_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id2, allow_same_message, &ioctl_take_msg_ret2);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_entry_id, -1);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_addr, 0);
  KUNIT_EXPECT_EQ(test, ioctl_take_msg_ret2.ret_pub_shm_info.publisher_num, 0);
}

void test_case_take_msg_too_many_mapping_processes(struct kunit * test)
{
  // Arrange: create MAX_PROCESS_NUM_PER_MEMPOOL processes which map to the same memory pool
  int ret;
  union ioctl_add_subscriber_args add_subscriber_args;
  union ioctl_add_publisher_args add_publisher_args;
  const pid_t publisher_pid = 1000;
  pid_t subscriber_pid = 2000;
  const uint32_t qos_depth = 1;
  const bool qos_transient_local = false;
  const bool allow_same_message = true;

  union ioctl_get_new_shm_args get_new_shm_args;
  ret = get_new_shm_addr(publisher_pid, PAGE_SIZE, &get_new_shm_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  int mmap_process_num = 1;
  for (int i = 0; i < MAX_PROCESS_NUM_PER_MEMPOOL / MAX_SUBSCRIBER_NUM + 1; i++) {
    char topic_name[50];
    snprintf(topic_name, sizeof(topic_name), "/kunit_test_topic%d", i);
    ret = add_publisher(
      topic_name, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, qos_depth,
      qos_transient_local, &add_publisher_args);
    KUNIT_ASSERT_EQ(test, ret, 0);
    for (int j = 0; j < MAX_SUBSCRIBER_NUM; j++) {
      if (mmap_process_num >= MAX_PROCESS_NUM_PER_MEMPOOL) {
        break;
      }
      ret = get_new_shm_addr(subscriber_pid, PAGE_SIZE, &get_new_shm_args);
      KUNIT_ASSERT_EQ(test, ret, 0);

      ret = add_subscriber(
        topic_name, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid++, qos_depth,
        qos_transient_local, IS_TAKE_SUB, &add_subscriber_args);
      KUNIT_ASSERT_EQ(test, ret, 0);
      union ioctl_take_msg_args take_msg_ret;
      ret = take_msg(
        topic_name, current->nsproxy->ipc_ns, add_subscriber_args.ret_id, allow_same_message,
        &take_msg_ret);
      KUNIT_ASSERT_EQ(test, ret, 0);
      mmap_process_num++;
    }
  }
  const char * topic_name = "/kunit_test_topic_1000";
  ret = add_publisher(
    topic_name, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, qos_depth, qos_transient_local,
    &add_publisher_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), MAX_PROCESS_NUM_PER_MEMPOOL);

  ret = get_new_shm_addr(subscriber_pid, PAGE_SIZE, &get_new_shm_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
  ret = add_subscriber(
    topic_name, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid, qos_depth, qos_transient_local,
    IS_TAKE_SUB, &add_subscriber_args);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act
  union ioctl_take_msg_args take_msg_ret;
  ret = take_msg(
    topic_name, current->nsproxy->ipc_ns, add_subscriber_args.ret_id, allow_same_message,
    &take_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -ENOBUFS);
}

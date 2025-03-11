#include "agnocast_kunit_receive_msg.h"

#include "../agnocast.h"

#include <kunit/test.h>

static char * topic_name = "/kunit_test_topic";
static char * node_name = "/kunit_test_node";
static bool qos_is_transient_local = false;
static bool is_take_sub = false;

static void setup_one_subscriber(
  struct kunit * test, pid_t subscriber_pid, uint32_t qos_depth, topic_local_id_t * subscriber_id)
{
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    topic_name, node_name, subscriber_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &subscriber_args);
  *subscriber_id = subscriber_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_publisher(
  struct kunit * test, pid_t publisher_pid, uint32_t qos_depth, topic_local_id_t * publisher_id,
  uint64_t * ret_addr)
{
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  *ret_addr = new_shm_args.ret_addr;

  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    topic_name, node_name, publisher_pid, qos_depth, qos_is_transient_local, &publisher_args);
  *publisher_id = publisher_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

void test_case_no_topic_when_receive(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id = 0;
  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_no_subscriber_when_receive(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 1, &publisher_id, &ret_addr);

  topic_local_id_t subscriber_id = 0;
  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_no_publish_no_receive(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 1, &subscriber_id);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_no_receive_since_volatile(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 1, &publisher_id, &ret_addr);
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(topic_name, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 1, &subscriber_id);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret2 = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_receive_one(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 1, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 1, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret1 = publish_msg(topic_name, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret2 = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 1);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_ids[0], ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(topic_name, subscriber_id),
    ioctl_receive_msg_ret.ret_entry_ids[0]);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_receive_based_on_qos_depth(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 10, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 1, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(topic_name, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  union ioctl_publish_args ioctl_publish_msg_ret2;
  int ret2 = publish_msg(topic_name, publisher_id, ret_addr + 1, &ioctl_publish_msg_ret2);
  KUNIT_ASSERT_EQ(test, ret2, 0);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret3 = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 1);
  KUNIT_EXPECT_EQ(
    test, ioctl_receive_msg_ret.ret_entry_ids[0], ioctl_publish_msg_ret2.ret_entry_id);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(topic_name, subscriber_id),
    ioctl_receive_msg_ret.ret_entry_ids[0]);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_too_many_rc(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 1, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 1, &subscriber_id);

  union ioctl_publish_args ioctl_publish_msg_ret1;
  int ret1 = publish_msg(topic_name, publisher_id, ret_addr, &ioctl_publish_msg_ret1);
  KUNIT_ASSERT_EQ(test, ret1, 0);

  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    int ret = increment_message_entry_rc(
      topic_name, subscriber_id + i + 1, ioctl_publish_msg_ret1.ret_entry_id);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret2 = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret2, -ENOBUFS);
}

void test_case_receive_max_qos_depth(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 10, &publisher_id, &ret_addr);
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 10, &subscriber_id);

  for (int i = 0; i < MAX_QOS_DEPTH - 1; i++) {
    union ioctl_publish_args ioctl_publish_msg_ret;
    int ret = publish_msg(topic_name, publisher_id, ret_addr, &ioctl_publish_msg_ret);
    KUNIT_ASSERT_EQ(test, ret, 0);
  }
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret = publish_msg(topic_name, publisher_id, ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret, 0);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret3 = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 10);
  KUNIT_EXPECT_EQ(
    test, get_latest_received_entry_id(topic_name, subscriber_id),
    ioctl_publish_msg_ret.ret_entry_id);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

// ================================================
// Tests for set_publisher_shm_info

void test_case_one_new_pub(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 10, &subscriber_id);
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 10, &publisher_id, &ret_addr);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 1);
}

void test_case_pubsub_in_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(1000, PAGE_SIZE, &new_shm_args);
  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    topic_name, node_name, 1000, 10, qos_is_transient_local, is_take_sub, &subscriber_args);
  union ioctl_publisher_args publisher_args;
  int ret3 =
    publisher_add(topic_name, node_name, 1000, 10, qos_is_transient_local, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret4 = receive_msg(topic_name, subscriber_args.ret_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_2pub_in_same_process(struct kunit * test)
{
  // Arrange

  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, 2000, 10, &subscriber_id);

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(1000, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args1;
  int ret2 =
    publisher_add(topic_name, node_name, 1000, 10, qos_is_transient_local, &publisher_args1);
  union ioctl_publisher_args publisher_args2;
  int ret3 =
    publisher_add(topic_name, node_name, 1000, 1, qos_is_transient_local, &publisher_args2);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;

  // Act
  int ret4 = receive_msg(topic_name, subscriber_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 1);
}

void test_case_2sub_in_same_process(struct kunit * test)
{
  // Arrange
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(2000, PAGE_SIZE, &new_shm_args);
  union ioctl_subscriber_args subscriber_args1;
  int ret2 = subscriber_add(
    topic_name, node_name, 2000, 10, qos_is_transient_local, is_take_sub, &subscriber_args1);
  union ioctl_subscriber_args subscriber_args2;
  int ret3 = subscriber_add(
    topic_name, node_name, 2000, 1, qos_is_transient_local, is_take_sub, &subscriber_args2);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);

  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  setup_one_publisher(test, 1000, 10, &publisher_id, &ret_addr);

  union ioctl_receive_msg_args ioctl_receive_msg_ret;
  int ret4 = receive_msg(topic_name, subscriber_args1.ret_id, &ioctl_receive_msg_ret);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_ASSERT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 1);

  // Act
  int ret5 = receive_msg(topic_name, subscriber_args2.ret_id, &ioctl_receive_msg_ret);

  // Assert
  KUNIT_EXPECT_EQ(test, ret5, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_entry_num, 0);
  KUNIT_EXPECT_EQ(test, ioctl_receive_msg_ret.ret_pub_shm_info.publisher_num, 0);
}

void test_case_too_many_mapping_processes(struct kunit * test)
{
  // TODO(Koichi98): Implement this test case
  KUNIT_EXPECT_EQ(test, 0, 0);
}

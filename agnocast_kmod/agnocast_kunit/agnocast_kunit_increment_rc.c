#include "agnocast_kunit_increment_rc.h"

#include "../agnocast.h"

#include <kunit/test.h>

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const uint32_t QOS_DEPTH = 10;
static const bool QOS_IS_TRANSIENT_LOCAL = false;
static pid_t subscriber_pid = 1000;
static pid_t publisher_pid = 2000;
static const bool IS_TAKE_SUB = false;

static void setup_one_publisher(
  struct kunit * test, topic_local_id_t * publisher_id, uint64_t * ret_addr)
{
  publisher_pid++;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  *ret_addr = new_shm_args.ret_addr;

  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, QOS_DEPTH,
    QOS_IS_TRANSIENT_LOCAL, &publisher_args);
  *publisher_id = publisher_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_subscriber(struct kunit * test, topic_local_id_t * subscriber_id)
{
  subscriber_pid++;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid, QOS_DEPTH,
    QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB, &subscriber_args);
  *subscriber_id = subscriber_args.ret_id;

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_entry(
  struct kunit * test, topic_local_id_t * publisher_id, int64_t * entry_id)
{
  uint64_t ret_addr;
  setup_one_publisher(test, publisher_id, &ret_addr);

  union ioctl_publish_args publish_args;
  int ret =
    publish_msg(TOPIC_NAME, current->nsproxy->ipc_ns, *publisher_id, ret_addr, &publish_args);

  KUNIT_ASSERT_EQ(test, ret, 0);

  *entry_id = publish_args.ret_entry_id;
}

void test_case_increment_rc(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  topic_local_id_t subscriber_id;
  int64_t entry_id;
  setup_one_entry(test, &publisher_id, &entry_id);
  setup_one_subscriber(test, &subscriber_id);

  // Act
  int ret_inc =
    increment_message_entry_rc(TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, entry_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret_inc, 0);
}

void test_case_increment_rc_without_topic(struct kunit * test)
{
  // Arrange
  const char * invalid_topic_name = "/kunit_test_topic_dummy";

  // Act
  int ret = increment_message_entry_rc(invalid_topic_name, current->nsproxy->ipc_ns, 0, 0);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_increment_rc_without_entry(struct kunit * test)
{
  // Arrange
  topic_local_id_t subscriber_id;
  setup_one_subscriber(test, &subscriber_id);
  const int64_t invalid_entry_id = -1;

  // Act
  int ret = increment_message_entry_rc(
    TOPIC_NAME, current->nsproxy->ipc_ns, subscriber_id, invalid_entry_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_increment_rc_by_publisher(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  int64_t entry_id;
  setup_one_entry(test, &publisher_id, &entry_id);

  // Act
  int ret =
    increment_message_entry_rc(TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, entry_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_increment_rc_by_invalid_pubsub_id(struct kunit * test)
{
  // Arrange
  topic_local_id_t publisher_id;
  int64_t entry_id;
  setup_one_entry(test, &publisher_id, &entry_id);
  topic_local_id_t invalid_pubsub_id = -1;

  // Act
  int ret =
    increment_message_entry_rc(TOPIC_NAME, current->nsproxy->ipc_ns, invalid_pubsub_id, entry_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

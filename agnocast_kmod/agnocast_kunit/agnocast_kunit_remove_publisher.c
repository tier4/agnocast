#include "agnocast_kunit_remove_publisher.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

#include <kunit/test.h>
#include <linux/delay.h>

// ==========================================
// 定数定義
// ==========================================
static const pid_t PID_BASE = 1000;
static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const uint32_t QOS_DEPTH = 1;
static const bool QOS_IS_TRANSIENT_LOCAL = false;
static const bool QOS_IS_RELIABLE = true;
static const bool IS_TAKE_SUB = false;
static const bool IGNORE_LOCAL_PUBLICATIONS = false;

// ==========================================
// セットアップ用ヘルパー関数 (Setup Helpers)
// ==========================================

static uint64_t setup_one_process(struct kunit * test, const pid_t pid)
{
  union ioctl_add_process_args ioctl_ret;
  int ret = add_process(pid, current->nsproxy->ipc_ns, &ioctl_ret);

  KUNIT_ASSERT_EQ(test, ret, 0);
  return ioctl_ret.ret_addr;
}

static topic_local_id_t setup_one_publisher(struct kunit * test, const pid_t publisher_pid)
{
  union ioctl_add_publisher_args add_publisher_args;
  int ret = add_publisher(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, publisher_pid, QOS_DEPTH,
    QOS_IS_TRANSIENT_LOCAL, &add_publisher_args);

  KUNIT_ASSERT_EQ(test, ret, 0);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));

  return add_publisher_args.ret_id;
}

static topic_local_id_t setup_one_subscriber(struct kunit * test, const pid_t subscriber_pid)
{
  union ioctl_add_subscriber_args add_subscriber_args;
  int ret = add_subscriber(
    TOPIC_NAME, current->nsproxy->ipc_ns, NODE_NAME, subscriber_pid, QOS_DEPTH,
    QOS_IS_TRANSIENT_LOCAL, QOS_IS_RELIABLE, IS_TAKE_SUB, IGNORE_LOCAL_PUBLICATIONS,
    &add_subscriber_args);

  KUNIT_ASSERT_EQ(test, ret, 0);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));

  return add_subscriber_args.ret_id;
}

static uint64_t setup_one_entry(
  struct kunit * test, const topic_local_id_t publisher_id, const uint64_t msg_virtual_address)
{
  union ioctl_publish_msg_args publish_msg_args;
  int ret = publish_msg(
    TOPIC_NAME, current->nsproxy->ipc_ns, publisher_id, msg_virtual_address, &publish_msg_args);

  KUNIT_ASSERT_EQ(test, ret, 0);
  KUNIT_ASSERT_TRUE(
    test, is_in_topic_entries(TOPIC_NAME, current->nsproxy->ipc_ns, publish_msg_args.ret_entry_id));

  return publish_msg_args.ret_entry_id;
}

// ==========================================
// テストケース (Publisher Removal)
// ==========================================

// Test case 1: Basic removal.
// Publisher is removed. Since no subscribers exist, the topic should be removed.
void test_case_remove_publisher_basic(struct kunit * test)
{
  // Arrange
  const pid_t pid = PID_BASE;
  setup_one_process(test, pid);
  const topic_local_id_t pub_id = setup_one_publisher(test, pid);

  // Check initial state
  KUNIT_ASSERT_EQ(test, get_topic_num(current->nsproxy->ipc_ns), 1);
  union ioctl_get_publisher_num_args get_pub_args;
  int ret = get_publisher_num(TOPIC_NAME, current->nsproxy->ipc_ns, &get_pub_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
  KUNIT_ASSERT_EQ(test, get_pub_args.ret_publisher_num, 1);

  // Act
  ret = remove_publisher(TOPIC_NAME, current->nsproxy->ipc_ns, pub_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);

  // Topic should be gone because it's empty
  KUNIT_EXPECT_EQ(test, get_topic_num(current->nsproxy->ipc_ns), 0);
  KUNIT_EXPECT_FALSE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));
}

// Test case 2: Removal with remaining subscriber.
// Publisher is removed, but a subscriber exists, so the topic must remain.
void test_case_remove_publisher_keeps_topic_with_subscriber(struct kunit * test)
{
  // Arrange
  const pid_t pid = PID_BASE;
  setup_one_process(test, pid);
  const topic_local_id_t pub_id = setup_one_publisher(test, pid);
  setup_one_subscriber(test, pid);  // Subscriberを作成

  // Act
  int ret = remove_publisher(TOPIC_NAME, current->nsproxy->ipc_ns, pub_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);

  // Topic should STILL exist because subscriber is there
  KUNIT_EXPECT_EQ(test, get_topic_num(current->nsproxy->ipc_ns), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));

  // Verify counts
  union ioctl_get_publisher_num_args get_pub_args;
  get_publisher_num(TOPIC_NAME, current->nsproxy->ipc_ns, &get_pub_args);
  KUNIT_EXPECT_EQ(test, get_pub_args.ret_publisher_num, 0);  // Publisherは0

  union ioctl_get_subscriber_num_args get_sub_args;
  get_subscriber_num(TOPIC_NAME, current->nsproxy->ipc_ns, &get_sub_args);
  KUNIT_EXPECT_EQ(test, get_sub_args.ret_subscriber_num, 1);  // Subscriberは1
}

// Test case 3: Message cleanup (No subscribers).
// Publisher published a message, but nobody is reading it.
// Removing publisher should delete the message and the topic.
void test_case_remove_publisher_cleans_unreferenced_messages(struct kunit * test)
{
  // Arrange
  const pid_t pid = PID_BASE;
  const uint64_t msg_addr = setup_one_process(test, pid);
  const topic_local_id_t pub_id = setup_one_publisher(test, pid);

  // Publish a message
  const uint64_t entry_id = setup_one_entry(test, pub_id, msg_addr);

  // Check message exists
  KUNIT_ASSERT_TRUE(test, is_in_topic_entries(TOPIC_NAME, current->nsproxy->ipc_ns, entry_id));

  // Act
  int ret = remove_publisher(TOPIC_NAME, current->nsproxy->ipc_ns, pub_id);

  // Assert
  KUNIT_EXPECT_EQ(test, ret, 0);

  // Message should be deleted (owned by pub, no subscribers)
  KUNIT_EXPECT_FALSE(test, is_in_topic_entries(TOPIC_NAME, current->nsproxy->ipc_ns, entry_id));

  // Topic should be gone
  KUNIT_EXPECT_FALSE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));
}

// Test case 4: Orphaned Message (Active Subscriber).
// Publisher published a message, and a subscriber is reading it.
// Removing publisher should remove PubInfo, but KEEP the message (as orphan).
void test_case_remove_publisher_leaves_orphaned_messages(struct kunit * test)
{
  // Arrange
  const pid_t pid = PID_BASE;
  const uint64_t msg_addr = setup_one_process(test, pid);
  const topic_local_id_t pub_id = setup_one_publisher(test, pid);
  const topic_local_id_t sub_id = setup_one_subscriber(test, pid);

  const uint64_t entry_id = setup_one_entry(test, pub_id, msg_addr);

  // Subscriber holds reference
  int ret = increment_message_entry_rc(TOPIC_NAME, current->nsproxy->ipc_ns, sub_id, entry_id);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Act
  ret = remove_publisher(TOPIC_NAME, current->nsproxy->ipc_ns, pub_id);
  KUNIT_ASSERT_EQ(test, ret, 0);

  // Assert
  // 1. Topic still exists (Subscriber is there)
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME, current->nsproxy->ipc_ns));

  // 2. Publisher info should be GONE (This is the key design choice)
  union ioctl_get_publisher_num_args get_pub_args;
  get_publisher_num(TOPIC_NAME, current->nsproxy->ipc_ns, &get_pub_args);
  KUNIT_EXPECT_EQ(test, get_pub_args.ret_publisher_num, 0);

  // 3. Message entry MUST still exist (because Subscriber has RC=1)
  KUNIT_EXPECT_TRUE(test, is_in_topic_entries(TOPIC_NAME, current->nsproxy->ipc_ns, entry_id));

  // 4. Verify RC state
  // Publisher's RC should be removed (implied by implementation logic)
  // Subscriber's RC should be 1
  KUNIT_EXPECT_EQ(test, get_entry_rc(TOPIC_NAME, current->nsproxy->ipc_ns, entry_id, sub_id), 1);
  KUNIT_EXPECT_EQ(test, get_entry_rc(TOPIC_NAME, current->nsproxy->ipc_ns, entry_id, pub_id), 0);
}
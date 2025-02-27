#include "agnocast_kunit_publish_msg.h"

#include "../agnocast.h"

#include <kunit/test.h>

// static int publish_msg_test_init(void);
// static int publish_msg_test_exit(void);
char * topic_name = "/kunit_test_topic";
char * node_name = "/kunit_test_node";
uint32_t qos_depth = 10;
bool qos_is_transient_local = false;
pid_t subscriber_pid = 1000;
pid_t publisher_pid = 2000;
bool is_take_sub = false;

static void setup_one_subscriber(struct kunit * test)
{
  subscriber_pid++;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, 1024, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    topic_name, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &subscriber_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_publisher(struct kunit * test)
{
  publisher_pid++;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, 1024, &new_shm_args);

  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    topic_name, node_name, publisher_pid, qos_depth, qos_is_transient_local, &publisher_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static int publish_msg_test_init(int qos_depth, bool transient_local)
{
  char * topic_name = "kunit_test_topic";
  union ioctl_publisher_args ioctl_ret;
  int ret = publisher_add(topic_name, 1, qos_depth, transient_local, &ioctl_ret);
  if (ret < 0) return ret;

  return 0;
}

// Expect to fail at find_topic()
void test_case_publish_msg_sample0(struct kunit * test)
{
  // Main test
  char * topic_name = "kunit_test_topic";
  topic_local_id_t publisher_id = 0;
  uint64_t msg_virtual_address = 0x40000000000;
  union ioctl_publish_args ioctl_publish_ret;
  int ret = publish_msg(topic_name, publisher_id, msg_virtual_address, &ioctl_publish_ret);

  KUNIT_EXPECT_EQ(test, -1, ret);
}

// Expect to fail at find_publisher_info
void test_case_publish_msg_sample1(struct kunit * test)
{
  pid_t pid = 1;
  uint64_t shm_size = 1000;
  union ioctl_new_shm_args ioctl_new_shm_ret;
  int ret1 = new_shm_addr(pid, shm_size, &ioctl_new_shm_ret);

  char * topic_name = "kunit_test_topic";
  uint32_t qos_depth = 1;
  bool qos_is_transient_local = true;
  pid_t subscriber_pid = 1;
  bool is_take_sub = false;
  union ioctl_subscriber_args ioctl_subscriber_ret;
  int ret2 = subscriber_add(
    topic_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &ioctl_subscriber_ret);

  // Main test
  topic_local_id_t publisher_id = 0;
  uint64_t msg_virtual_address = 0x40000000000;
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret3 = publish_msg(topic_name, publisher_id, msg_virtual_address, &ioctl_publish_msg_ret);

  KUNIT_ASSERT_EQ(test, 1, ret1);
  KUNIT_EXPECT_EQ(test, 1, ret2);
  KUNIT_EXPECT_EQ(test, -1, ret3);
}

// Expect to fail at insert_message_entry - "New message..."
// Since it is an unreachable code, this test is skipped.

// Expect to go through at "if (pub_info->entries_num <= pub_info->qos_depth)" in
// release_msgs_to_meet_depth
void test_case_publish_msg_sample2(struct kunit * test)
{
  // Setup
  pid_t pid = 1;
  uint64_t shm_size = 1000;
  union ioctl_new_shm_args ioctl_new_shm_ret;
  int ret1 = new_shm_addr(pid, shm_size, &ioctl_new_shm_ret);

  char * topic_name = "kunit_test_topic";
  uint32_t qos_depth = 1;
  bool qos_is_transient_local = true;
  pid_t publisher_pid = 1;
  bool is_take_sub = false;
  union ioctl_publisher_args ioctl_publisher_ret;
  int ret2 = publisher_add(
    topic_name, publisher_pid, qos_depth, qos_is_transient_local, is_take_sub,
    &ioctl_publisher_ret);

  topic_local_id_t publisher_id = 0;
  uint64_t msg_virtual_address = 0x40000000000;
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret3 = publish_msg(topic_name, publisher_id, msg_virtual_address, &ioctl_publish_msg_ret);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ioctl_publish_msg_ret.ret_released_num, 0);
}

// Expect to fail at release_msgs_to_meet_depth - "For some reason..."
void test_case_publish_msg_sample3(struct kunit * test)
{
  // create publisher1 qos1
  // for 100 + 1 times
  // publish once
  // increment rc
  // decrement rc MAX_RELEASE_NUM+1 times
  // publish again
  // check error
}

// Expect to fail at release_msgs_to_meet_depth - "Failed to get message entries..."
// This is also unreachable.

// Expect to fail at release_msgs_to_meet_depth - "entries_num is inconsistent..."
// This is also unreachable.

// Expect to go through "if (en->publisher_id != pub_info->id) continue" in
// release_msgs_to_meet_depth
void test_case_publish_msg_sample4(struct kunit * test)
{
  // create publisher1 qos1
  // publish once
  // create publisher2 qos1
  // publish twice
  // increment the entry_node that the publishe1 has created and check if it is still there.
  // increment_rc()
}

// Expect to go through "if(is_referenced(en)) continue;" in release_msgs_to_meet_depth
void test_case_publish_msg_sample4(struct kunit * test)
{
  // create publisher1 qos1
  // publish once
  // increment the entry_node ref count
  // publish again
  // increment the first entry_node ref count and check if it is still there. increment_rc()
}

// Expect to return at the end in release_msgs_to_meet_depth (release 1)
void test_case_publish_msg_sample5(struct kunit * test)
{
  // create publisher1 qos1
  // publish once
  // publish again
  // check release_num is 1
}

// Expect to return at the end in release_msgs_to_meet_depth (should release more then
// MAX_RELEASE_NUM)
void test_case_publish_msg_sample6(struct kunit * test)
{
  // create publisher1 qos1
  // for MAX_RELEASE_NUM + 1times
  // publish once
  // increment rc
  // decrement rc MAX_RELEASE_NUM+1 times
  // publish again
  // check release_num is MAX_RELEASE_NUM without error
}
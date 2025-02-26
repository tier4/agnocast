#include "agnocast_kunit_publish_msg.h"

#include "../agnocast.h"

#include <kunit/test.h>

// static int publish_msg_test_init(void);
// static int publish_msg_test_exit(void);

static int publish_msg_test_init(int qos_depth, bool transient_local)
{
  char * topic_name = "kunit_test_topic";
  union ioctl_publisher_args ioctl_ret;
  int ret = publisher_add(topic_name, 1, qos_depth, transient_local, &ioctl_ret);
  if (ret < 0) return ret;

  return 0;
}

// static int publish_msg_test_init(int qos_depth, bool transient_local)
//{

// return 0;
//}

// static int publish_msg_test_exit()
//{
// return 0;
//}

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
  union ioctl_publish_args ioctl_publish_ret;
  int ret3 = publish_msg(topic_name, publisher_id, msg_virtual_address, &ioctl_publish_ret);

  KUNIT_EXPECT_EQ(test, 0, ret1);
  KUNIT_EXPECT_EQ(test, 0, ret2);
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
  pid_t subscriber_pid = 1;
  bool is_take_sub = false;
  union ioctl_publisher_args ioctl_publisher_ret;
  int ret2 = publisher_add(
    topic_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &ioctl_publisher_ret);

  KUNIT_EXPECT_EQ(test, 0, ret1);
  KUNIT_EXPECT_EQ(test, 0, ret2);
  KUNIT_EXPECT_EQ(test, -1, ret3);
}

// Expect to fail at release_msgs_to_meet_depth - "For some reason..."

// Expect to fail at release_msgs_to_meet_depth - "Failed to get message entries..."

// Expect to fail at release_msgs_to_meet_depth - "entries_num is inconsistent..."

// Expect to go through "if (en->publisher_id != pub_info->id) continue" in
// release_msgs_to_meet_depth

// Expect to go through "if(is_referenced(en)) continue;" in release_msgs_to_meet_depth

// Expect to return at the end in release_msgs_to_meet_depth
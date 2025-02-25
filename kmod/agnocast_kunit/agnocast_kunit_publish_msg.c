#include "agnocast_kunit_publish_msg.h"

#include "../agnocast.h"

#include <kunit/test.h>

static int publish_msg_test_init(void);
static int publish_msg_test_exit(void);

static int publish_msg_test_init(int qos_depth, bool transient_local)
{
  char * topic_name = "kunit_test_topic";
  union ioctl_publisher_args ioctl_ret;
  int ret = publisher_add(topic_name, 1, qos_depth, transient_local, &ioctl_ret);
  if (ret < 0) return ret;

  return 0;
}

static int publish_msg_test_exit()
{
  return 0;
}

// Expect to fail at find_topic()
void test_case_publish_msg_sample0(struct kunit * test)
{
  // Setup
  KUNIT_ASSERT_EQ(test, 0, publish_msg_test_init(10, true));

  // Main test
  topic_local_id_t publisher_id = 0;
  uint64_t msg_virtual_address = 0x40000000000;

  KUNIT_EXPECT_EQ(test, 1 + 1, 2);

  // Teardown
  KUNIT_ASSERT_EQ(test, 0, publish_msg_test_exit());
}

// Expect to fail at find_publisher_info
void test_case_publish_msg_sample1(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 * 1, 1);
}

// Expect to fail at insert_message_entry - "New message..."

// Expect to fail at insert_message_entry - "Insert a message..."

// Expect to fail at release_msgs_to_meet_depth - "For some reason..."

// Expect to fail at release_msgs_to_meet_depth - "Failed to get message entries..."

// Expect to fail at release_msgs_to_meet_depth - "entries_num is inconsistent..."

// Expect to go through "if (en->publisher_id != pub_info->id) continue" in
// release_msgs_to_meet_depth

// Expect to go through "if(is_referenced(en)) continue;" in release_msgs_to_meet_depth

// Expect to return at the end in release_msgs_to_meet_depth
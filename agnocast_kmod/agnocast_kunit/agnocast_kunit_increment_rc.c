
#include "agnocast_kunit_increment_rc.h"

#include "../agnocast.h"

#include <kunit/test.h>


static char * topic_name = "/kunit_test_topic";
static char * node_name = "/kunit_test_node";
static uint32_t qos_depth = 10;
static bool qos_is_transient_local = false;
static pid_t publisher_pid = 2000;

static void setup_one_publisher(
  struct kunit * test, topic_local_id_t * publisher_id, uint64_t * ret_addr)
{
  publisher_pid++;

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

void test_case_increment_rc(struct kunit * test)
{
  union ioctl_publish_args publish_args;
  topic_local_id_t publisher_id;
  uint64_t ret_addr;
  
  setup_one_publisher(test, &publisher_id, &ret_addr);

  int ret_pub = publish_msg(topic_name, publisher_id, ret_addr, &publish_args);
  KUNIT_ASSERT_EQ(test, ret_pub, 0);
  int64_t entry_id = publish_args.ret_entry_id;

  int ret_inc = increment_message_entry_rc(topic_name, 2, entry_id);
  KUNIT_EXPECT_EQ(test, ret_inc, 0);

  int ret_inc_fail = increment_message_entry_rc(topic_name, publisher_id, entry_id);
  KUNIT_EXPECT_EQ(test, ret_inc_fail, -1);
}

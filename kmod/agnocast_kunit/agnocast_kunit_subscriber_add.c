#include "agnocast_kunit_subscriber_add.h"

#include "../agnocast.h"

#include <kunit/test.h>

// Feel free to delete this test case
void test_case_subscriber_add_sample0(struct kunit * test)
{
  char * topic_name = "my_topic";
  uint32_t qos_depth = 5;
  uint32_t subscriber_pid = 123;
  bool is_take_sub = false;

  union ioctl_new_shm_args args1;
  int ret1 = new_shm_addr(subscriber_pid, 1000, &args1);

  union ioctl_subscriber_args args2;
  int ret2 = subscriber_add(topic_name, qos_depth, subscriber_pid, is_take_sub, &args2);

  union ioctl_get_subscriber_num_args args3;
  int ret3 = get_subscriber_num(topic_name, &args3);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, args3.ret_subscriber_num, 1);
}

// Feel free to delete this test case
void test_case_subscriber_add_sample1(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 + 1, 2);
}

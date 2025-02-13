#include "agnocast_kunit_subscriber_add.h"

#include "../agnocast.h"

#include <kunit/test.h>

void test_case_subscriber_add(struct kunit * test)
{
  char * topic_name = "my_topic";
  uint32_t qos_depth = 5;
  uint32_t subscriber_pid = 123;
  uint64_t init_timestamp = 12345;
  bool is_take_sub = false;

  union ioctl_subscriber_args args;
  int ret =
    subscriber_add(topic_name, qos_depth, subscriber_pid, init_timestamp, is_take_sub, &args);

  union ioctl_get_subscriber_num_args args2;
  int ret2 = get_subscriber_num(topic_name, &args2);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, args2.ret_subscriber_num, 1);
}
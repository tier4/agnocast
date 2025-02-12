#include "agnocast.h"

#include <kunit/test.h>

MODULE_LICENSE("Dual BSD/GPL");

static void test_case_subscriber_add(struct kunit * test)
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

static void agnocast_sample_test_case(struct kunit * test)
{
  printk("hoge");
  tmp_func();
  KUNIT_EXPECT_EQ(test, 1 + 1, 2);
}

struct kunit_case agnocast_test_cases[] = {
  KUNIT_CASE(agnocast_sample_test_case),
  KUNIT_CASE(test_case_subscriber_add),
  {},
};

static int agnocast_test_init(struct kunit * test)
{
  return 0;
}

static void agnocast_test_exit(struct kunit * test)
{
  agnocast_exit_free_data();
}

static int agnocast_test_suite_init(struct kunit_suite * test_suite)
{
  agnocast_init_mutexes();
  agnocast_init_device();

  int ret;

  ret = agnocast_init_kthread();
  if (ret < 0) return ret;

  ret = agnocast_init_kprobe();
  if (ret < 0) return ret;

  return 0;
}

static void agnocast_test_suite_exit(struct kunit_suite * test_suite)
{
  agnocast_exit_kprobe();
  agnocast_exit_kthread();
  agnocast_exit_device();
}

struct kunit_suite agnocast_test_suite = {
  .name = "agnocast_test_suite",
  .init = agnocast_test_init,
  .exit = agnocast_test_exit,
  .suite_init = agnocast_test_suite_init,
  .suite_exit = agnocast_test_suite_exit,
  .test_cases = agnocast_test_cases,
};

kunit_test_suite(agnocast_test_suite);

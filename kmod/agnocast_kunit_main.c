#include "agnocast.h"

#include <kunit/test.h>

MODULE_LICENSE("Dual BSD/GPL");

static void agnocast_sample_test_case(struct kunit * test)
{
  printk("hoge");
  tmp_func();
  KUNIT_EXPECT_EQ(test, 1 + 1, 2);
}

struct kunit_case agnocast_test_cases[] = {
  KUNIT_CASE(agnocast_sample_test_case),
  {},
};

static int agnocast_test_init(struct kunit * test)
{
  int ret;
  agnocast_init_device();

  ret = agnocast_init_kthread();
  if (ret < 0) return ret;

  ret = agnocast_init_kprobe();
  if (ret < 0) return ret;

  return 0;
}

static void agnocast_test_exit(struct kunit * test)
{
  agnocast_exit_free_data();
  agnocast_exit_kthread();
  agnocast_exit_kprobe();
  agnocast_exit_device();
}

static int agnocast_test_suite_init(struct kunit_suite * test_suite)
{
  agnocast_init_mutexes();
  return 0;
}

static void agnocast_test_suite_exit(struct kunit_suite * test_suite)
{
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

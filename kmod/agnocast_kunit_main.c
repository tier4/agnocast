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
  return 0;
}

static void agnocast_test_exit(struct kunit * test)
{
}

static int agnocast_test_suite_init(struct kunit_suite * test_suite)
{
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

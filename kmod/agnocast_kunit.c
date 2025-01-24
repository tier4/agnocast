#include "agnocast.h"

#include <kunit/test.h>

MODULE_LICENSE("Dual BSD/GPL");

static void agnocast_sample_test_case(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 + 1, 2);
}

struct kunit_case agnocast_test_cases[] = {
  KUNIT_CASE(agnocast_sample_test_case),
  {},
};

struct kunit_suite agnocast_test_suite = {
  .name = "agnocast_test_suite",
  .test_cases = agnocast_test_cases,
};

kunit_test_suite(agnocast_test_suite);

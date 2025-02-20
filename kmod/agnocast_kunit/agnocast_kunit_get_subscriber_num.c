#include "agnocast_kunit_get_subscriber_num.h"

#include "../agnocast.h"

#include <kunit/test.h>

// Feel free to delete this test case
void test_case_get_subscriber_num_sample0(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 + 1, 2);
}

// Feel free to delete this test case
void test_case_get_subscriber_num_sample1(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 * 1, 1);
}

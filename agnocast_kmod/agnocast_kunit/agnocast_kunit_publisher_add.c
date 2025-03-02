#include "agnocast_kunit_publisher_add.h"

#include "../agnocast.h"

#include <kunit/test.h>

// Feel free to delete this test case
void test_case_publisher_add_sample0(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 + 1, 2);
}

// Feel free to delete this test case
void test_case_publisher_add_sample1(struct kunit * test)
{
  KUNIT_EXPECT_EQ(test, 1 * 1, 1);
}

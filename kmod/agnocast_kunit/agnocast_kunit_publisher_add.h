#include <kunit/test.h>

#define TEST_CASES_PUBLISHER_ADD \
  KUNIT_CASE(test_case_publisher_add_sample0), KUNIT_CASE(test_case_publisher_add_sample1)

void test_case_publisher_add_sample0(struct kunit * test);
void test_case_publisher_add_sample1(struct kunit * test);

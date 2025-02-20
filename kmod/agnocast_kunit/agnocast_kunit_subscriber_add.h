#include <kunit/test.h>

#define TEST_CASES_SUBSCRIBER_ADD \
  KUNIT_CASE(test_case_subscriber_add_sample0), KUNIT_CASE(test_case_subscriber_add_sample1)

void test_case_subscriber_add_sample0(struct kunit * test);
void test_case_subscriber_add_sample1(struct kunit * test);
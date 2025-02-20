#include <kunit/test.h>

#define TEST_CASES_GET_SUBSCRIBER_NUM \
  KUNIT_CASE(test_case_get_subscriber_num_sample0), KUNIT_CASE(test_case_get_subscriber_num_sample1)

void test_case_get_subscriber_num_sample0(struct kunit * test);
void test_case_get_subscriber_num_sample1(struct kunit * test);

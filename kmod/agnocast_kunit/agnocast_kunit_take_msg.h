#include <kunit/test.h>

#define TEST_CASES_TAKE_MSG \
  KUNIT_CASE(test_case_take_msg_sample0), KUNIT_CASE(test_case_take_msg_sample1)

void test_case_take_msg_sample0(struct kunit * test);
void test_case_take_msg_sample1(struct kunit * test);

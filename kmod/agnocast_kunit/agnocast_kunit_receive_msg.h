#include <kunit/test.h>

#define TEST_CASES_RECEIVE_MSG \
  KUNIT_CASE(test_case_receive_msg_sample0), KUNIT_CASE(test_case_receive_msg_sample1)

void test_case_receive_msg_sample0(struct kunit * test);
void test_case_receive_msg_sample1(struct kunit * test);

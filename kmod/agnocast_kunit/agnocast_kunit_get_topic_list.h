#include <kunit/test.h>

#define TEST_CASES_GET_TOPIC_LIST \
  KUNIT_CASE(test_case_get_topic_list_sample0), KUNIT_CASE(test_case_get_topic_list_sample1)

void test_case_get_topic_list_sample0(struct kunit * test);
void test_case_get_topic_list_sample1(struct kunit * test);

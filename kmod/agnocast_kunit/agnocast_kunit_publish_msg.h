#pragma once
#include <kunit/test.h>

#define TEST_CASES_PUBLISH_MSG \
  KUNIT_CASE(test_case_publish_msg_sample0), KUNIT_CASE(test_case_publish_msg_sample1)

void test_case_publish_msg_sample0(struct kunit * test);
void test_case_publish_msg_sample1(struct kunit * test);

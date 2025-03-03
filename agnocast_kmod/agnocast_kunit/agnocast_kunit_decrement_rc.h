#pragma once
#include <kunit/test.h>

#define TEST_CASES_DECREMENT_RC \
  KUNIT_CASE(test_case_decrement_rc_sample0), KUNIT_CASE(test_case_decrement_rc_sample1)

void test_case_decrement_rc_sample0(struct kunit * test);
void test_case_decrement_rc_sample1(struct kunit * test);

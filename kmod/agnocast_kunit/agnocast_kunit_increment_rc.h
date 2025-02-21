#pragma once
#include <kunit/test.h>

#define TEST_CASES_INCREMENT_RC \
  KUNIT_CASE(test_case_increment_rc_sample0), KUNIT_CASE(test_case_increment_rc_sample1)

void test_case_increment_rc_sample0(struct kunit * test);
void test_case_increment_rc_sample1(struct kunit * test);

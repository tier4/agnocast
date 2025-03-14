#pragma once
#include <kunit/test.h>

#define TEST_CASES_INCREMENT_RC KUNIT_CASE(test_case_increment_rc)

void test_case_increment_rc(struct kunit * test);

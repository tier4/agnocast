#pragma once
#include <kunit/test.h>

#define TEST_CASES_DO_EXIT KUNIT_CASE(test_case_do_exit), KUNIT_CASE(test_case_do_exit_many)

void test_case_do_exit(struct kunit * test);
void test_case_do_exit_many(struct kunit * test);

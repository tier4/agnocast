#pragma once
#include <kunit/test.h>

#define TEST_CASES_RECEIVE_MSG KUNIT_CASE(test_case_no_topic), KUNIT_CASE(test_case_no_subscriber)

void test_case_no_topic(struct kunit * test);
void test_case_no_subscriber(struct kunit * test);
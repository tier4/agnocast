#pragma once
#include <kunit/test.h>

#define TEST_CASES_REMOVE_PUBLISHER                                                               \
  KUNIT_CASE(test_case_remove_publisher_normal), KUNIT_CASE(test_case_remove_publisher_with_msg), \
    KUNIT_CASE(test_case_remove_publisher_invalid_id)

void test_case_remove_publisher_normal(struct kunit * test);
void test_case_remove_publisher_with_msg(struct kunit * test);
void test_case_remove_publisher_invalid_id(struct kunit * test);
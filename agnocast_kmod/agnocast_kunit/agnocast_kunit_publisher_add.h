#pragma once
#include <kunit/test.h>

#define TEST_CASES_PUBLISHER_ADD                                                        \
  KUNIT_CASE(test_case_publisher_add_normal), KUNIT_CASE(test_case_publisher_add_many), \
    KUNIT_CASE(test_case_publisher_add_too_many)

void test_case_publisher_add_normal(struct kunit * test);
void test_case_publisher_add_many(struct kunit * test);
void test_case_publisher_add_too_many(struct kunit * test);

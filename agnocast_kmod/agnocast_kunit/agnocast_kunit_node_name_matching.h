#pragma once
#include <kunit/test.h>

#define TEST_CASES_NODE_NAME_MATCHING                                                          \
  KUNIT_CASE(test_case_sub_exact_match), KUNIT_CASE(test_case_sub_prefix_no_match),            \
    KUNIT_CASE(test_case_pub_exact_match), KUNIT_CASE(test_case_pub_prefix_no_match),          \
    KUNIT_CASE(test_case_get_version)

void test_case_sub_exact_match(struct kunit * test);
void test_case_sub_prefix_no_match(struct kunit * test);
void test_case_pub_exact_match(struct kunit * test);
void test_case_pub_prefix_no_match(struct kunit * test);
void test_case_get_version(struct kunit * test);

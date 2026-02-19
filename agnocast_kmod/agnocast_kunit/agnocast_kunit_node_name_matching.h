#pragma once
#include <kunit/test.h>

#define TEST_CASES_NODE_NAME_MATCHING                                                               \
  KUNIT_CASE(test_case_subscriber_node_exact_match),                                                \
    KUNIT_CASE(test_case_subscriber_node_no_prefix_match),                                          \
    KUNIT_CASE(test_case_publisher_node_exact_match),                                               \
    KUNIT_CASE(test_case_publisher_node_no_prefix_match),                                           \
    KUNIT_CASE(test_case_get_version_returns_valid_string)

void test_case_subscriber_node_exact_match(struct kunit * test);
void test_case_subscriber_node_no_prefix_match(struct kunit * test);
void test_case_publisher_node_exact_match(struct kunit * test);
void test_case_publisher_node_no_prefix_match(struct kunit * test);
void test_case_get_version_returns_valid_string(struct kunit * test);

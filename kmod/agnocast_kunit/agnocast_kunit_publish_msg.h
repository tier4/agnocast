#pragma once
#include <kunit/test.h>

#define TEST_CASES_PUBLISH_MSG                                        \
  KUNIT_CASE(test_case_no_topic), KUNIT_CASE(test_case_no_publisher), \
    KUNIT_CASE(test_case_simple_publish_without_any_release),         \
    KUNIT_CASE(test_case_excessive_unreleased_entry_nodes),           \
    KUNIT_CASE(test_case_different_publisher_no_release),             \
    KUNIT_CASE(test_case_referenced_node_not_released),               \
    KUNIT_CASE(test_case_single_release_return), KUNIT_CASE(test_case_excessive_release_count)

void test_case_no_topic(struct kunit * test);
void test_case_no_publisher(struct kunit * test);
void test_case_simple_publish_without_any_release(struct kunit * test);
void test_case_excessive_unreleased_entry_nodes(struct kunit * test);
void test_case_different_publisher_no_release(struct kunit * test);
void test_case_referenced_node_not_released(struct kunit * test);
void test_case_single_release_return(struct kunit * test);
void test_case_excessive_release_count(struct kunit * test);
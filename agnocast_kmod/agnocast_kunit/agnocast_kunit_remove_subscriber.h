#pragma once
#include <kunit/test.h>

#define TEST_CASES_REMOVE_SUBSCRIBER                                    \
  KUNIT_CASE(test_case_remove_subscriber_basic),                        \
    KUNIT_CASE(test_case_remove_subscriber_keeps_topic_with_publisher), \
    KUNIT_CASE(test_case_remove_subscriber_clears_references)

void test_case_remove_subscriber_basic(struct kunit * test);
void test_case_remove_subscriber_keeps_topic_with_publisher(struct kunit * test);
void test_case_remove_subscriber_clears_references(struct kunit * test);
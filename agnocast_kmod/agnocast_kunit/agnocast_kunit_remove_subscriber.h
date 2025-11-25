#pragma once
#include <kunit/test.h>

#define TEST_CASES_REMOVE_SUBSCRIBER                    \
  KUNIT_CASE(test_case_remove_subscriber_normal),       \
    KUNIT_CASE(test_case_remove_subscriber_invalid_id), \
    KUNIT_CASE(test_case_remove_subscriber_invalid_topic)

void test_case_remove_subscriber_normal(struct kunit * test);
void test_case_remove_subscriber_invalid_id(struct kunit * test);
void test_case_remove_subscriber_invalid_topic(struct kunit * test);
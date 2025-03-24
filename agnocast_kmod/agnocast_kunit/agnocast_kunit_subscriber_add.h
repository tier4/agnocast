#pragma once
#include <kunit/test.h>

#define TEST_CASES_SUBSCRIBER_ADD                                                                \
  KUNIT_CASE(test_case_subscriber_add_normal), KUNIT_CASE(test_case_subscriber_add_invalid_qos), \
    KUNIT_CASE(test_case_subscriber_add_too_many_subscribers)

void test_case_subscriber_add_normal(struct kunit * test);
void test_case_subscriber_add_invalid_qos(struct kunit * test);
void test_case_subscriber_add_too_many_subscribers(struct kunit * test);

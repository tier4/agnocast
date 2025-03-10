#pragma once
#include <kunit/test.h>

#define TEST_CASES_RECEIVE_MSG                                                                    \
  KUNIT_CASE(test_case_no_topic1), KUNIT_CASE(test_case_no_subscriber),                           \
    KUNIT_CASE(test_case_no_publish_no_receive), KUNIT_CASE(test_case_no_receive_since_volatile), \
    KUNIT_CASE(test_case_receive_one), KUNIT_CASE(test_case_receive_based_on_qos_depth),          \
    KUNIT_CASE(test_case_too_many_rc), KUNIT_CASE(test_case_receive_max_qos_depth)

void test_case_no_topic1(struct kunit * test);
void test_case_no_subscriber(struct kunit * test);
void test_case_no_publish_no_receive(struct kunit * test);
void test_case_no_receive_since_volatile(struct kunit * test);
void test_case_receive_one(struct kunit * test);
void test_case_receive_based_on_qos_depth(struct kunit * test);
void test_case_too_many_rc(struct kunit * test);
void test_case_receive_max_qos_depth(struct kunit * test);
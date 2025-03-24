#pragma once
#include <kunit/test.h>

#define TEST_CASES_DECREMENT_RC                                                               \
  KUNIT_CASE(test_case_decrement_rc_no_topic), KUNIT_CASE(test_case_decrement_rc_no_message), \
    KUNIT_CASE(test_case_decrement_rc_no_pubsub_id),                                          \
    KUNIT_CASE(test_case_decrement_rc_last_reference),                                        \
    KUNIT_CASE(test_case_decrement_rc_multi_reference)

void test_case_decrement_rc_no_topic(struct kunit * test);
void test_case_decrement_rc_no_message(struct kunit * test);
void test_case_decrement_rc_no_pubsub_id(struct kunit * test);
void test_case_decrement_rc_last_reference(struct kunit * test);
void test_case_decrement_rc_multi_reference(struct kunit * test);

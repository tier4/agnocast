#pragma once
#include <kunit/test.h>

#define TEST_CASES_INCREMENT_RC                                                         \
  KUNIT_CASE(test_case_increment_rc), KUNIT_CASE(test_case_increment_rc_without_topic), \
    KUNIT_CASE(test_case_increment_rc_without_entry),                                   \
    KUNIT_CASE(test_case_increment_rc_by_publisher),                                    \
    KUNIT_CASE(test_case_increment_rc_by_invalid_pubsub_id)

void test_case_increment_rc(struct kunit * test);
void test_case_increment_rc_without_topic(struct kunit * test);
void test_case_increment_rc_without_entry(struct kunit * test);
void test_case_increment_rc_by_publisher(struct kunit * test);
void test_case_increment_rc_by_invalid_pubsub_id(struct kunit * test);

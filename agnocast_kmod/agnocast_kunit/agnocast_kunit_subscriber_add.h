#pragma once
#include <kunit/test.h>

#define TEST_CASES_SUBSCRIBER_ADD                                                        \
  KUNIT_CASE(test_case_subscriber_add_normal),                                           \
    KUNIT_CASE(test_case_subscriber_add_normal_with_publisher),                          \
    KUNIT_CASE(test_case_subscriber_add_normal_with_publisher_of_same_process),          \
    KUNIT_CASE(test_case_subscriber_add_normal_with_subscriber_of_same_process),         \
    KUNIT_CASE(test_case_subscriber_add_normal_with_many_publishers_of_same_process),    \
    KUNIT_CASE(test_case_subscriber_add_normal_with_entry_and_transient_local),          \
    KUNIT_CASE(test_case_subscriber_add_normal_with_many_entries_and_transient_local_1), \
    KUNIT_CASE(test_case_subscriber_add_normal_with_many_entries_and_transient_local_2), \
    KUNIT_CASE(test_case_subscriber_add_normal_with_many_entries_and_transient_local_3), \
    KUNIT_CASE(test_case_subscriber_add_invalid_qos),                                    \
    KUNIT_CASE(test_case_subscriber_add_without_self_process),                           \
    KUNIT_CASE(test_case_subscriber_add_too_many_mmap)

void test_case_subscriber_add_normal(struct kunit * test);
void test_case_subscriber_add_normal_with_publisher(struct kunit * test);
void test_case_subscriber_add_normal_with_publisher_of_same_process(struct kunit * test);
void test_case_subscriber_add_normal_with_subscriber_of_same_process(struct kunit * test);
void test_case_subscriber_add_normal_with_many_publishers_of_same_process(struct kunit * test);
void test_case_subscriber_add_normal_with_entry_and_transient_local(struct kunit * test);
void test_case_subscriber_add_normal_with_many_entries_and_transient_local_1(struct kunit * test);
void test_case_subscriber_add_normal_with_many_entries_and_transient_local_2(struct kunit * test);
void test_case_subscriber_add_normal_with_many_entries_and_transient_local_3(struct kunit * test);
void test_case_subscriber_add_invalid_qos(struct kunit * test);
void test_case_subscriber_add_too_many_subscribers(struct kunit * test);
void test_case_subscriber_add_without_self_process(struct kunit * test);
void test_case_subscriber_add_without_publisher_process(struct kunit * test);
void test_case_subscriber_add_too_many_mmap(struct kunit * test);

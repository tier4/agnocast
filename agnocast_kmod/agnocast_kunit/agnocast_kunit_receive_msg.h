#pragma once
#include <kunit/test.h>

#define TEST_CASES_RECEIVE_MSG                                                                   \
  KUNIT_CASE(test_case_no_topic_when_receive), KUNIT_CASE(test_case_no_subscriber_when_receive), \
    KUNIT_CASE(test_case_no_publish_no_receive), KUNIT_CASE(test_case_receive_one),              \
    KUNIT_CASE(test_case_receive_based_on_qos_depth), KUNIT_CASE(test_case_too_many_rc),         \
    KUNIT_CASE(test_case_receive_max_qos_depth), KUNIT_CASE(test_case_one_new_pub),              \
    KUNIT_CASE(test_case_pubsub_in_same_process), KUNIT_CASE(test_case_2pub_in_same_process),    \
    KUNIT_CASE(test_case_2sub_in_same_process), KUNIT_CASE(test_case_too_many_mapping_processes)

void test_case_no_topic_when_receive(struct kunit * test);
void test_case_no_subscriber_when_receive(struct kunit * test);
void test_case_no_publish_no_receive(struct kunit * test);
void test_case_receive_one(struct kunit * test);
void test_case_receive_based_on_qos_depth(struct kunit * test);
void test_case_too_many_rc(struct kunit * test);
void test_case_receive_max_qos_depth(struct kunit * test);
void test_case_one_new_pub(struct kunit * test);
void test_case_pubsub_in_same_process(struct kunit * test);
void test_case_2pub_in_same_process(struct kunit * test);
void test_case_2sub_in_same_process(struct kunit * test);
void test_case_too_many_mapping_processes(struct kunit * test);
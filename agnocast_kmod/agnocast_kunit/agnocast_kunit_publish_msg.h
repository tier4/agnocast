#pragma once
#include <kunit/test.h>

#define TEST_CASES_PUBLISH_MSG                                                                \
  KUNIT_CASE(test_case_publish_msg_no_topic), KUNIT_CASE(test_case_publish_msg_no_publisher), \
    KUNIT_CASE(test_case_publish_msg_simple_publish_without_any_release),                     \
    KUNIT_CASE(test_case_publish_msg_different_publisher_no_release),                         \
    KUNIT_CASE(test_case_publish_msg_referenced_node_not_released),                           \
    KUNIT_CASE(test_case_publish_msg_single_release_return),                                  \
    KUNIT_CASE(test_case_publish_msg_excessive_release_count),                                \
    KUNIT_CASE(test_case_publish_msg_ret_one_subscriber),                                     \
    KUNIT_CASE(test_case_publish_msg_ret_many_subscribers)

void test_case_publish_msg_no_topic(struct kunit * test);
void test_case_publish_msg_no_publisher(struct kunit * test);
void test_case_publish_msg_simple_publish_without_any_release(struct kunit * test);
void test_case_publish_msg_different_publisher_no_release(struct kunit * test);
void test_case_publish_msg_referenced_node_not_released(struct kunit * test);
void test_case_publish_msg_single_release_return(struct kunit * test);
void test_case_publish_msg_excessive_release_count(struct kunit * test);
void test_case_publish_msg_ret_one_subscriber(struct kunit * test);
void test_case_publish_msg_ret_many_subscribers(struct kunit * test);

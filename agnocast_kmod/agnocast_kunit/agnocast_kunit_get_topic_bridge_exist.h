#pragma once
#include <kunit/test.h>

#define TEST_CASES_GET_TOPIC_BRIDGE_EXIST                           \
  KUNIT_CASE(test_case_get_topic_bridge_exist_no_topic),            \
    KUNIT_CASE(test_case_get_topic_bridge_exist_normal_nodes),      \
    KUNIT_CASE(test_case_get_topic_bridge_exist_publisher_bridge),  \
    KUNIT_CASE(test_case_get_topic_bridge_exist_subscriber_bridge), \
    KUNIT_CASE(test_case_get_topic_bridge_exist_both_bridges)

void test_case_get_topic_bridge_exist_no_topic(struct kunit * test);
void test_case_get_topic_bridge_exist_normal_nodes(struct kunit * test);
void test_case_get_topic_bridge_exist_publisher_bridge(struct kunit * test);
void test_case_get_topic_bridge_exist_subscriber_bridge(struct kunit * test);
void test_case_get_topic_bridge_exist_both_bridges(struct kunit * test);

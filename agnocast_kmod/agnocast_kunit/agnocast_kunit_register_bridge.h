#pragma once
#include <kunit/test.h>

#define TEST_CASES_REGISTER_BRIDGE                                                               \
  KUNIT_CASE(test_case_register_bridge_normal), KUNIT_CASE(test_case_register_bridge_duplicate), \
    KUNIT_CASE(test_case_register_bridge_multi_topic)

void test_case_register_bridge_normal(struct kunit * test);
void test_case_register_bridge_duplicate(struct kunit * test);
void test_case_register_bridge_multi_topic(struct kunit * test);
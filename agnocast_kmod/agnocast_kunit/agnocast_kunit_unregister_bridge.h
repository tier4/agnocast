#pragma once
#include <kunit/test.h>

#define TEST_CASES_UNREGISTER_BRIDGE \
  KUNIT_CASE(test_case_unregister_bridge_normal), KUNIT_CASE(test_case_unregister_bridge_not_exist)

void test_case_unregister_bridge_normal(struct kunit * test);
void test_case_unregister_bridge_not_exist(struct kunit * test);
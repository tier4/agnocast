#ifndef SUBSCRIBER_TESTS_H
#define SUBSCRIBER_TESTS_H

#include <kunit/test.h>

#define SUBSCRIBER_TEST_CASES KUNIT_CASE(test_case_subscriber_add)

void test_case_subscriber_add(struct kunit * test);

#endif /* SUBSCRIBER_TESTS_H */

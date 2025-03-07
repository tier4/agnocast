#pragma once
#include <kunit/test.h>

#define TEST_CASES_NEW_SHM                                                          \
  KUNIT_CASE(test_case_new_shm_normal), KUNIT_CASE(test_case_new_shm_many),         \
    KUNIT_CASE(test_case_new_shm_not_aligned), KUNIT_CASE(test_case_new_shm_twice), \
    KUNIT_CASE(test_case_new_shm_too_big), KUNIT_CASE(test_case_new_shm_too_many)

void test_case_new_shm_normal(struct kunit * test);
void test_case_new_shm_many(struct kunit * test);
void test_case_new_shm_not_aligned(struct kunit * test);
void test_case_new_shm_twice(struct kunit * test);
void test_case_new_shm_too_big(struct kunit * test);
void test_case_new_shm_too_many(struct kunit * test);

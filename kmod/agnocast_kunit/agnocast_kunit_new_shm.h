#include <kunit/test.h>

#define TEST_CASES_NEW_SHM \
  KUNIT_CASE(test_case_new_shm_sample0), KUNIT_CASE(test_case_new_shm_sample1)

void test_case_new_shm_sample0(struct kunit * test);
void test_case_new_shm_sample1(struct kunit * test);

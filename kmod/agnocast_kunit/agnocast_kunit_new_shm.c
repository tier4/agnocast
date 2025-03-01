#include "agnocast_kunit_new_shm.h"

#include "../agnocast.h"

#include <kunit/test.h>

static pid_t pid = 1000;

void test_case_new_shm_normal(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);

  uint64_t local_pid = pid++;
  union ioctl_new_shm_args args;
  int ret = new_shm_addr(local_pid, PAGE_SIZE, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(local_pid));

  process_exit_cleanup(local_pid);
}

void test_case_new_shm_too_big(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);

  uint64_t local_pid = pid++;
  uint64_t shm_size = 8589934592 /* 8GB */ + PAGE_SIZE;
  union ioctl_new_shm_args args;
  int ret = new_shm_addr(local_pid, shm_size, &args);

  KUNIT_EXPECT_EQ(test, ret, -ENOMEM);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(local_pid));
}

void test_case_new_shm_too_many(struct kunit * test)
{
  const int process_num = 10000;
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);

  // ================================================
  // Act

  for (int i = 0; i < process_num; i++) {
    uint64_t local_pid = pid++;
    union ioctl_new_shm_args args;
    new_shm_addr(local_pid, PAGE_SIZE, &args);
  }

  uint64_t local_pid = pid++;
  union ioctl_new_shm_args args;
  int ret = new_shm_addr(local_pid, PAGE_SIZE, &args);

  // ================================================
  // Assert

  KUNIT_EXPECT_EQ(test, ret, -ENOMEM);
  KUNIT_EXPECT_TRUE(test, get_proc_info_htable_size() > 0);
  KUNIT_EXPECT_TRUE(test, get_proc_info_htable_size() < process_num);
  KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(local_pid));

  for (int i = 0; i < process_num; i++) {
    process_exit_cleanup(pid - process_num + i);
  }
}

void test_case_new_shm_not_aligned(struct kunit * test)
{
  uint64_t local_pid = pid++;
  union ioctl_new_shm_args args;
  int ret = new_shm_addr(local_pid, PAGE_SIZE + 1, &args);

  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}

void test_case_new_shm_twice(struct kunit * test)
{
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);

  pid_t local_pid = pid++;
  union ioctl_new_shm_args args;
  int ret1 = new_shm_addr(local_pid, PAGE_SIZE, &args);
  int ret2 = new_shm_addr(local_pid, PAGE_SIZE, &args);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, -EINVAL);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(local_pid));

  process_exit_cleanup(local_pid);
}

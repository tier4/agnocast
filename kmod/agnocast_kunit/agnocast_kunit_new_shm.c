#include "agnocast_kunit_new_shm.h"

#include "../agnocast.h"

#include <kunit/test.h>

static pid_t pid = 1000;

static uint64_t get_previously_allocated_shm_addr(struct kunit * test)
{
  uint64_t local_pid = pid++;
  union ioctl_new_shm_args new_shm_args;
  int ret = new_shm_addr(local_pid, PAGE_SIZE, &new_shm_args);
  KUNIT_ASSERT_EQ(test, ret, 0);
  process_exit_cleanup(local_pid);
  return new_shm_args.ret_addr;
}

void test_case_new_shm_normal(struct kunit * test)
{
  uint64_t previously_allocated_shm_addr = get_previously_allocated_shm_addr(test);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);

  uint64_t local_pid = pid++;
  union ioctl_new_shm_args args;
  int ret = new_shm_addr(local_pid, PAGE_SIZE, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_addr, previously_allocated_shm_addr + PAGE_SIZE);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(local_pid));
}

void test_case_new_shm_many(struct kunit * test)
{
  const int process_num = 1000;
  uint64_t previously_allocated_shm_addr = get_previously_allocated_shm_addr(test);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);

  // ================================================
  // Act

  pid_t local_pid_start = pid;
  for (int i = 0; i < process_num - 1; i++) {
    uint64_t local_pid = pid++;
    union ioctl_new_shm_args args;
    new_shm_addr(local_pid, PAGE_SIZE, &args);
  }

  uint64_t local_pid = pid++;
  union ioctl_new_shm_args args;
  int ret = new_shm_addr(local_pid, PAGE_SIZE, &args);

  // ================================================
  // Assert

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_addr, previously_allocated_shm_addr + PAGE_SIZE * process_num);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), process_num);
  for (int i = 0; i < process_num; i++) {
    KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(local_pid_start + i));
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
}

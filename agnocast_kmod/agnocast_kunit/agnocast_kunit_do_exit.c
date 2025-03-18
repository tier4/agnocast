#include "agnocast_kunit_do_exit.h"

#include "../agnocast.h"

#include <kunit/test-bug.h>
#include <kunit/test.h>
#include <linux/delay.h>

static struct kprobe p;
static struct pt_regs regs;

static const pid_t PID_BASE = 1000;

static void setup_processes(struct kunit * test, const int process_num)
{
  union ioctl_new_shm_args ioctl_ret;
  for (int i = 0; i < process_num; i++) {
    const pid_t pid = PID_BASE + i;
    int ret = new_shm_addr(pid, PAGE_SIZE, &ioctl_ret);
    KUNIT_ASSERT_EQ(test, ret, 0);
    KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(pid));
  }
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), process_num);
}

void test_case_do_exit(struct kunit * test)
{
  // Arrange
  const int process_num = 1;
  setup_processes(test, process_num);

  // Act
  current->pid = PID_BASE;
  pre_handler_do_exit(&p, &regs);

  msleep(10);  // wait for exit_worker_thread to handle process exit

  // Assert
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(PID_BASE));
}

void test_case_do_exit_many(struct kunit * test)
{
  // Arrange
  const int process_num = EXIT_QUEUE_SIZE;
  setup_processes(test, process_num);

  // Act
  for (int i = 0; i < process_num; i++) {
    current->pid = PID_BASE + i;
    pre_handler_do_exit(&p, &regs);
  }

  msleep(100);  // wait for exit_worker_thread to handle process exit

  // Assert
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 0);
  for (int i = 0; i < process_num; i++) {
    const pid_t pid = PID_BASE + i;
    KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(pid));
  }
}

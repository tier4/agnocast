#include "agnocast_kunit_do_exit.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

#include <kunit/test.h>
#include <linux/delay.h>

static const pid_t PID_BASE = 1000;

static const char * TOPIC_NAME = "/kunit_test_topic";
static const char * NODE_NAME = "/kunit_test_node";
static const uint32_t QOS_DEPTH = 1;
static const bool QOS_IS_TRANSIENT_LOCAL = false;
static const bool IS_TAKE_SUB = false;

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
  enqueue_exit_pid(PID_BASE);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(PID_BASE));
}

void test_case_do_exit_many(struct kunit * test)
{
  // Arrange
  const int agnocast_process_num = MEMPOOL_TOTAL_NUM;
  const int non_agnocast_process_num = EXIT_QUEUE_SIZE - agnocast_process_num;
  setup_processes(test, agnocast_process_num);

  // Act
  for (int i = 0; i < agnocast_process_num + non_agnocast_process_num; i++) {
    const pid_t pid = PID_BASE + i;
    enqueue_exit_pid(pid);
  }

  // wait for exit_worker_thread to handle process exit:
  // this value is conservatively estimated to be large enough
  msleep(100);

  // Assert
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  for (int i = 0; i < agnocast_process_num; i++) {
    const pid_t pid = PID_BASE + i;
    KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(pid));
  }
}

void test_case_do_exit_with_publisher(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = PID_BASE;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args.ret_id));

  // Act
  enqueue_exit_pid(publisher_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 0);
}

void test_case_do_exit_with_subscriber(struct kunit * test)
{
  // Arrange
  const pid_t subscriber_pid = PID_BASE;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret3 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args.ret_id));

  // Act
  enqueue_exit_pid(subscriber_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret4 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 0);
}

// Test case for process exit where there are two publishers and subscribers in one process
void test_case_do_exit_with_many_pubsub_in_one_process(struct kunit * test)
{
  // Arrange
  const pid_t pid = PID_BASE;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(pid, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args1, publisher_args2;
  int ret2 =
    publisher_add(TOPIC_NAME, NODE_NAME, pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args1);
  int ret3 =
    publisher_add(TOPIC_NAME, NODE_NAME, pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args2);
  union ioctl_subscriber_args subscriber_args1, subscriber_args2;
  int ret4 = subscriber_add(
    TOPIC_NAME, NODE_NAME, pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB, &subscriber_args1);
  int ret5 = subscriber_add(
    TOPIC_NAME, NODE_NAME, pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB, &subscriber_args2);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret6 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ret5, 0);
  KUNIT_ASSERT_EQ(test, ret6, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(pid));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 2);
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 2);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args2.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args2.ret_id));

  // Act
  enqueue_exit_pid(pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret7 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret7, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 0);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 0);
}

// Test case for process exit where there are two publishers and subscribers in different processes
// and one publisher exits
void test_case_do_exit_with_many_pubsub_in_different_processes_and_publisher_exit(
  struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid1 = PID_BASE;
  const pid_t publisher_pid2 = PID_BASE + 1;
  const pid_t subscriber_pid1 = PID_BASE + 2;
  const pid_t subscriber_pid2 = PID_BASE + 3;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid1, PAGE_SIZE, &new_shm_args);
  int ret2 = new_shm_addr(publisher_pid2, PAGE_SIZE, &new_shm_args);
  int ret3 = new_shm_addr(subscriber_pid1, PAGE_SIZE, &new_shm_args);
  int ret4 = new_shm_addr(subscriber_pid2, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args1, publisher_args2;
  int ret5 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid1, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args1);
  int ret6 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid2, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args2);
  union ioctl_subscriber_args subscriber_args1, subscriber_args2;
  int ret7 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid1, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args1);
  int ret8 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid2, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args2);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret9 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ret5, 0);
  KUNIT_ASSERT_EQ(test, ret6, 0);
  KUNIT_ASSERT_EQ(test, ret7, 0);
  KUNIT_ASSERT_EQ(test, ret8, 0);
  KUNIT_ASSERT_EQ(test, ret9, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 4);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid2));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid2));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 2);
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 2);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args2.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args2.ret_id));

  // Act
  enqueue_exit_pid(publisher_pid1);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret10 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret10, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 3);
  KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(publisher_pid1));
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(publisher_pid2));
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(subscriber_pid1));
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(subscriber_pid2));
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 2);
  KUNIT_EXPECT_FALSE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args1.ret_id));
  KUNIT_EXPECT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args2.ret_id));
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args1.ret_id));
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args2.ret_id));
}

// Test case for process exit where there are two publishers and subscribers in different processes
// and one subscriber exits
void test_case_do_exit_with_many_pubsub_in_different_processes_and_subscriber_exit(
  struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid1 = PID_BASE;
  const pid_t publisher_pid2 = PID_BASE + 1;
  const pid_t subscriber_pid1 = PID_BASE + 2;
  const pid_t subscriber_pid2 = PID_BASE + 3;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid1, PAGE_SIZE, &new_shm_args);
  int ret2 = new_shm_addr(publisher_pid2, PAGE_SIZE, &new_shm_args);
  int ret3 = new_shm_addr(subscriber_pid1, PAGE_SIZE, &new_shm_args);
  int ret4 = new_shm_addr(subscriber_pid2, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args1, publisher_args2;
  int ret5 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid1, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args1);
  int ret6 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid2, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args2);
  union ioctl_subscriber_args subscriber_args1, subscriber_args2;
  int ret7 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid1, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args1);
  int ret8 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid2, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args2);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret9 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ret5, 0);
  KUNIT_ASSERT_EQ(test, ret6, 0);
  KUNIT_ASSERT_EQ(test, ret7, 0);
  KUNIT_ASSERT_EQ(test, ret8, 0);
  KUNIT_ASSERT_EQ(test, ret9, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 4);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid2));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid2));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 2);
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 2);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args2.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args2.ret_id));

  // Act
  enqueue_exit_pid(subscriber_pid1);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret10 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret10, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 3);
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(publisher_pid1));
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(publisher_pid2));
  KUNIT_EXPECT_FALSE(test, is_in_proc_info_htable(subscriber_pid1));
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(subscriber_pid2));
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 2);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args1.ret_id));
  KUNIT_EXPECT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args2.ret_id));
  KUNIT_EXPECT_FALSE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args1.ret_id));
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args2.ret_id));
}

// Test case for process exit where there are two publishers and subscribers in different processes
// and all publishers and subscribers exit
void test_case_do_exit_with_many_pubsub_in_different_processes_and_all_pubsub_exit(
  struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid1 = PID_BASE;
  const pid_t publisher_pid2 = PID_BASE + 1;
  const pid_t subscriber_pid1 = PID_BASE + 2;
  const pid_t subscriber_pid2 = PID_BASE + 3;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid1, PAGE_SIZE, &new_shm_args);
  int ret2 = new_shm_addr(publisher_pid2, PAGE_SIZE, &new_shm_args);
  int ret3 = new_shm_addr(subscriber_pid1, PAGE_SIZE, &new_shm_args);
  int ret4 = new_shm_addr(subscriber_pid2, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args1, publisher_args2;
  int ret5 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid1, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args1);
  int ret6 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid2, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args2);
  union ioctl_subscriber_args subscriber_args1, subscriber_args2;
  int ret7 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid1, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args1);
  int ret8 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid2, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args2);
  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret9 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ret5, 0);
  KUNIT_ASSERT_EQ(test, ret6, 0);
  KUNIT_ASSERT_EQ(test, ret7, 0);
  KUNIT_ASSERT_EQ(test, ret8, 0);
  KUNIT_ASSERT_EQ(test, ret9, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 4);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid2));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid1));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid2));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 2);
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 2);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args2.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args1.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args2.ret_id));

  // Act
  enqueue_exit_pid(publisher_pid1);
  enqueue_exit_pid(publisher_pid2);
  enqueue_exit_pid(subscriber_pid1);
  enqueue_exit_pid(subscriber_pid2);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret10 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret10, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 0);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 0);
}

void test_case_do_exit_with_entry(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = PID_BASE;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args);
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret3 =
    publish_msg(TOPIC_NAME, publisher_args.ret_id, new_shm_args.ret_addr, &ioctl_publish_msg_ret);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args.ret_id));
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_entries(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id));
  KUNIT_ASSERT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, publisher_args.ret_id), 1);

  // Act
  enqueue_exit_pid(publisher_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 0);
  KUNIT_EXPECT_EQ(test, get_topic_entries_num(TOPIC_NAME), 0);
}

// Test case for process exit order: publisher exits first, then subscriber exits
void test_case_do_exit_with_multi_references_publisher_exit_first(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = PID_BASE;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args);
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret3 =
    publish_msg(TOPIC_NAME, publisher_args.ret_id, new_shm_args.ret_addr, &ioctl_publish_msg_ret);

  const pid_t subscriber_pid = PID_BASE + 1;
  int ret4 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_subscriber_args subscriber_args;
  int ret5 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args);
  int ret6 = increment_message_entry_rc(
    TOPIC_NAME, subscriber_args.ret_id, ioctl_publish_msg_ret.ret_entry_id);

  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret7 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ret5, 0);
  KUNIT_ASSERT_EQ(test, ret6, 0);
  KUNIT_ASSERT_EQ(test, ret7, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 2);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args.ret_id));
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_entries(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id));
  KUNIT_ASSERT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, publisher_args.ret_id), 1);
  KUNIT_ASSERT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, subscriber_args.ret_id), 1);

  // Act
  enqueue_exit_pid(publisher_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret8 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret8, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_EXPECT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args.ret_id));
  KUNIT_EXPECT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args.ret_id));
  KUNIT_EXPECT_EQ(test, get_topic_entries_num(TOPIC_NAME), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_entries(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id));
  KUNIT_EXPECT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, subscriber_args.ret_id), 1);

  // Act
  enqueue_exit_pid(subscriber_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret9 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret9, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 0);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 0);
  KUNIT_EXPECT_EQ(test, get_topic_entries_num(TOPIC_NAME), 0);
}

// Test case for process exit order: subscriber exits first, then publisher exits
void test_case_do_exit_with_multi_references_subscriber_exit_first(struct kunit * test)
{
  // Arrange
  const pid_t publisher_pid = PID_BASE;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(publisher_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_publisher_args publisher_args;
  int ret2 = publisher_add(
    TOPIC_NAME, NODE_NAME, publisher_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, &publisher_args);
  union ioctl_publish_args ioctl_publish_msg_ret;
  int ret3 =
    publish_msg(TOPIC_NAME, publisher_args.ret_id, new_shm_args.ret_addr, &ioctl_publish_msg_ret);

  const pid_t subscriber_pid = PID_BASE + 1;
  int ret4 = new_shm_addr(subscriber_pid, PAGE_SIZE, &new_shm_args);
  union ioctl_subscriber_args subscriber_args;
  int ret5 = subscriber_add(
    TOPIC_NAME, NODE_NAME, subscriber_pid, QOS_DEPTH, QOS_IS_TRANSIENT_LOCAL, IS_TAKE_SUB,
    &subscriber_args);
  int ret6 = increment_message_entry_rc(
    TOPIC_NAME, subscriber_args.ret_id, ioctl_publish_msg_ret.ret_entry_id);

  union ioctl_get_subscriber_num_args get_subscriber_num_args;
  int ret7 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
  KUNIT_ASSERT_EQ(test, ret3, 0);
  KUNIT_ASSERT_EQ(test, ret4, 0);
  KUNIT_ASSERT_EQ(test, ret5, 0);
  KUNIT_ASSERT_EQ(test, ret6, 0);
  KUNIT_ASSERT_EQ(test, ret7, 0);
  KUNIT_ASSERT_EQ(test, get_proc_info_htable_size(), 2);
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(publisher_pid));
  KUNIT_ASSERT_TRUE(test, is_in_proc_info_htable(subscriber_pid));
  KUNIT_ASSERT_EQ(test, get_topic_num(), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_ASSERT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 1);
  KUNIT_ASSERT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args.ret_id));
  KUNIT_ASSERT_TRUE(test, is_in_subscriber_htable(TOPIC_NAME, subscriber_args.ret_id));
  KUNIT_ASSERT_EQ(test, get_topic_entries_num(TOPIC_NAME), 1);
  KUNIT_ASSERT_TRUE(test, is_in_topic_entries(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id));
  KUNIT_ASSERT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, publisher_args.ret_id), 1);
  KUNIT_ASSERT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, subscriber_args.ret_id), 1);

  // Act
  enqueue_exit_pid(subscriber_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret8 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret8, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_proc_info_htable(publisher_pid));
  KUNIT_EXPECT_EQ(test, get_topic_num(), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_htable(TOPIC_NAME));
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 1);
  KUNIT_EXPECT_TRUE(test, is_in_publisher_htable(TOPIC_NAME, publisher_args.ret_id));
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 0);
  KUNIT_EXPECT_EQ(test, get_topic_entries_num(TOPIC_NAME), 1);
  KUNIT_EXPECT_TRUE(test, is_in_topic_entries(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id));
  KUNIT_EXPECT_EQ(
    test, get_entry_rc(TOPIC_NAME, ioctl_publish_msg_ret.ret_entry_id, publisher_args.ret_id), 1);

  // Act
  enqueue_exit_pid(publisher_pid);

  // wait for exit_worker_thread to handle process exit
  msleep(10);

  // Assert
  int ret9 = get_subscriber_num(TOPIC_NAME, &get_subscriber_num_args);
  KUNIT_EXPECT_EQ(test, ret9, 0);
  KUNIT_EXPECT_EQ(test, get_proc_info_htable_size(), 0);
  KUNIT_EXPECT_EQ(test, get_topic_num(), 0);
  KUNIT_EXPECT_EQ(test, get_publisher_num(TOPIC_NAME), 0);
  KUNIT_EXPECT_EQ(test, get_subscriber_num_args.ret_subscriber_num, 0);
}

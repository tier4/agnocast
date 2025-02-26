#include "agnocast_kunit_get_subscriber_num.h"

#include "../agnocast.h"

#include <kunit/test.h>

void test_case_get_subscriber_num_normal(struct kunit * test)
{
  char * topic_name = "/my_topic";
  char * node_name = "/my_node";
  uint32_t qos_depth = 10;
  bool qos_is_transient_local = false;
  pid_t subscriber_pid = 123;
  bool is_take_sub = false;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, 1024, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    topic_name, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &subscriber_args);

  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret3 = get_subscriber_num(topic_name, &subscriber_num_args);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 1);
}

void test_case_get_subscriber_num_many(struct kunit * test)
{
  char * topic_name = "/my_topic";

  for (int i = 1; i <= MAX_SUBSCRIBER_NUM; i++) {
    char node_name_buf[32];
    snprintf(node_name_buf, sizeof(node_name_buf), "/my_node%d", i);

    char * node_name = node_name_buf;
    uint32_t qos_depth = (i % MAX_QOS_DEPTH) + 1;
    bool qos_is_transient_local = (i % 2) == 0;
    pid_t subscriber_pid = 123 + i;
    bool is_take_sub = (i % 2) == 0;

    union ioctl_new_shm_args new_shm_args;
    int ret1 = new_shm_addr(subscriber_pid, 1024, &new_shm_args);

    union ioctl_subscriber_args subscriber_args;
    int ret2 = subscriber_add(
      topic_name, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
      &subscriber_args);

    union ioctl_get_subscriber_num_args subscriber_num_args;
    int ret3 = get_subscriber_num(topic_name, &subscriber_num_args);

    KUNIT_EXPECT_EQ(test, ret1, 0);
    KUNIT_EXPECT_EQ(test, ret2, 0);
    KUNIT_EXPECT_EQ(test, ret3, 0);
    KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, i);
  }
}

void test_case_get_subscriber_num_different_topic(struct kunit * test)
{
  char * topic_name1 = "/my_topic1";
  char * topic_name2 = "/my_topic2";
  char * node_name = "/my_node";
  uint32_t qos_depth = 10;
  bool qos_is_transient_local = false;
  pid_t subscriber_pid = 123;
  bool is_take_sub = false;

  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid, 1024, &new_shm_args);

  union ioctl_subscriber_args subscriber_args1;
  int ret2 = subscriber_add(
    topic_name1, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &subscriber_args1);

  union ioctl_subscriber_args subscriber_args2;
  int ret3 = subscriber_add(
    topic_name2, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &subscriber_args2);

  union ioctl_get_subscriber_num_args subscriber_num_args1;
  int ret4 = get_subscriber_num(topic_name1, &subscriber_num_args1);

  union ioctl_get_subscriber_num_args subscriber_num_args2;
  int ret5 = get_subscriber_num(topic_name2, &subscriber_num_args2);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ret5, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args1.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_num_args2.ret_subscriber_num, 1);
}

void test_case_get_subscriber_num_with_exit(struct kunit * test)
{
  char * topic_name = "/my_topic";
  char * node_name = "/my_node";
  uint32_t qos_depth = 10;
  bool qos_is_transient_local = false;
  bool is_take_sub = false;

  pid_t subscriber_pid1 = 123;
  union ioctl_new_shm_args new_shm_args;
  int ret1 = new_shm_addr(subscriber_pid1, 1024, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  int ret2 = subscriber_add(
    topic_name, node_name, qos_depth, qos_is_transient_local, subscriber_pid1, is_take_sub,
    &subscriber_args);

  pid_t subscriber_pid2 = 124;
  union ioctl_new_shm_args new_shm_args2;
  int ret3 = new_shm_addr(subscriber_pid2, 1024, &new_shm_args2);

  union ioctl_subscriber_args subscriber_args2;
  int ret4 = subscriber_add(
    topic_name, node_name, qos_depth, qos_is_transient_local, subscriber_pid2, is_take_sub,
    &subscriber_args2);

  union ioctl_get_subscriber_num_args subscriber_num_args1;
  int ret5 = get_subscriber_num(topic_name, &subscriber_num_args1);

  process_exit_cleanup(subscriber_pid1);

  union ioctl_get_subscriber_num_args subscriber_num_args2;
  int ret6 = get_subscriber_num(topic_name, &subscriber_num_args2);

  process_exit_cleanup(subscriber_pid2);

  union ioctl_get_subscriber_num_args subscriber_num_args3;
  int ret7 = get_subscriber_num(topic_name, &subscriber_num_args3);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, ret3, 0);
  KUNIT_EXPECT_EQ(test, ret4, 0);
  KUNIT_EXPECT_EQ(test, ret5, 0);
  KUNIT_EXPECT_EQ(test, ret6, 0);
  KUNIT_EXPECT_EQ(test, ret7, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args1.ret_subscriber_num, 2);
  KUNIT_EXPECT_EQ(test, subscriber_num_args2.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_num_args3.ret_subscriber_num, 0);
}

#include "agnocast_kunit_get_subscriber_num.h"

#include "../agnocast.h"

#include <kunit/test.h>

char * topic_name = "/my_topic";
char * node_name = "/my_node";
uint32_t qos_depth = 10;
bool qos_is_transient_local = false;
pid_t subscriber_pid = 1000;
pid_t publisher_pid = 2000;
bool is_take_sub = false;

static void setup_one_subscriber(void)
{
  subscriber_pid++;

  union ioctl_new_shm_args new_shm_args;
  new_shm_addr(subscriber_pid, 1024, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  subscriber_add(
    topic_name, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &subscriber_args);
}

static void setup_one_publisher(void)
{
  publisher_pid++;

  union ioctl_new_shm_args new_shm_args;
  new_shm_addr(publisher_pid, 1024, &new_shm_args);

  union ioctl_publisher_args publisher_args;
  publisher_add(
    topic_name, node_name, publisher_pid, qos_depth, qos_is_transient_local, &publisher_args);
}

static void setup_different_topic_subscriber(char * topic_name2)
{
  subscriber_pid++;

  union ioctl_new_shm_args new_shm_args;
  new_shm_addr(subscriber_pid, 1024, &new_shm_args);

  union ioctl_subscriber_args subscriber_args;
  subscriber_add(
    topic_name2, node_name, qos_depth, qos_is_transient_local, subscriber_pid, is_take_sub,
    &subscriber_args);
}

void test_case_get_subscriber_num_normal(struct kunit * test)
{
  setup_one_subscriber();

  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret = get_subscriber_num(topic_name, &subscriber_num_args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 1);
}

void test_case_get_subscriber_num_many(struct kunit * test)
{
  for (int i = 0; i < MAX_SUBSCRIBER_NUM; i++) {
    setup_one_subscriber();
  }

  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret = get_subscriber_num(topic_name, &subscriber_num_args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, MAX_SUBSCRIBER_NUM);
}

void test_case_get_subscriber_num_different_topic(struct kunit * test)
{
  char * topic_name2 = "/my_topic2";
  setup_one_subscriber();
  setup_different_topic_subscriber(topic_name2);

  union ioctl_get_subscriber_num_args subscriber_num_args1;
  union ioctl_get_subscriber_num_args subscriber_num_args2;
  int ret1 = get_subscriber_num(topic_name, &subscriber_num_args1);
  int ret2 = get_subscriber_num(topic_name2, &subscriber_num_args2);

  KUNIT_EXPECT_EQ(test, ret1, 0);
  KUNIT_EXPECT_EQ(test, ret2, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args1.ret_subscriber_num, 1);
  KUNIT_EXPECT_EQ(test, subscriber_num_args2.ret_subscriber_num, 1);
}

void test_case_get_subscriber_num_with_exit(struct kunit * test)
{
  setup_one_subscriber();

  union ioctl_get_subscriber_num_args subscriber_num_args;
  process_exit_cleanup(subscriber_pid);
  int ret = get_subscriber_num(topic_name, &subscriber_num_args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 0);
}

void test_case_get_subscriber_num_no_subscriber(struct kunit * test)
{
  setup_one_publisher();

  union ioctl_get_subscriber_num_args subscriber_num_args;
  int ret = get_subscriber_num(topic_name, &subscriber_num_args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, subscriber_num_args.ret_subscriber_num, 0);
}

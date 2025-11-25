#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"
#include "agnocast_kunit_get_filtered_publisher_num.h"

static char * node_name = "/kunit_test_node";
static uint32_t qos_depth = 10;
static bool qos_is_transient_local = false;
static pid_t subscriber_pid = 3000;
static pid_t publisher_pid = 4000;
static bool is_take_sub = false;

static void setup_one_subscriber(struct kunit * test, char * topic_name)
{
  subscriber_pid++;

  union ioctl_add_process_args add_process_args;
  int ret1 = add_process(subscriber_pid, current->nsproxy->ipc_ns, &add_process_args);

  union ioctl_add_subscriber_args add_subscriber_args;
  int ret2 = add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, subscriber_pid, qos_depth,
    qos_is_transient_local, is_take_sub, &add_subscriber_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

static void setup_one_publisher(struct kunit * test, char * topic_name)
{
  publisher_pid++;
  union ioctl_add_process_args add_process_args;
  int ret1 = add_process(publisher_pid, current->nsproxy->ipc_ns, &add_process_args);

  union ioctl_add_publisher_args add_publisher_args;
  int ret2 = add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, publisher_pid, qos_depth,
    qos_is_transient_local, &add_publisher_args);

  KUNIT_ASSERT_EQ(test, ret1, 0);
  KUNIT_ASSERT_EQ(test, ret2, 0);
}

void test_case_get_filtered_publisher_num_normal(struct kunit * test)
{
  char * topic_name = "/kunit_test_ext_pub_normal";
  setup_one_publisher(test, topic_name);

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = 0};
  int ret = get_filtered_publisher_num(topic_name, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, 1);
}

void test_case_get_filtered_publisher_num_exclude_self(struct kunit * test)
{
  char * topic_name = "/kunit_test_ext_pub_exclude_self";
  setup_one_publisher(test, topic_name);
  pid_t target_pid = publisher_pid;

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = target_pid};
  int ret = get_filtered_publisher_num(topic_name, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, 0);
}

void test_case_get_filtered_publisher_num_exclude_other(struct kunit * test)
{
  char * topic_name = "/kunit_test_ext_pub_exclude_other";

  setup_one_publisher(test, topic_name);
  pid_t pid_a = publisher_pid;

  setup_one_publisher(test, topic_name);

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = pid_a};
  int ret = get_filtered_publisher_num(topic_name, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, 1);
}

void test_case_get_filtered_publisher_num_many(struct kunit * test)
{
  char * topic_name = "/kunit_test_ext_pub_many";
  pid_t target_pid = 0;

  for (int i = 0; i < MAX_PUBLISHER_NUM; i++) {
    setup_one_publisher(test, topic_name);
    if (i == MAX_PUBLISHER_NUM / 2) target_pid = publisher_pid;
  }

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = target_pid};
  int ret = get_filtered_publisher_num(topic_name, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, MAX_PUBLISHER_NUM - 1);
}

void test_case_get_filtered_publisher_num_different_topic(struct kunit * test)
{
  char * topic_1 = "/kunit_test_ext_pub_diff_1";
  char * topic_2 = "/kunit_test_ext_pub_diff_2";

  setup_one_publisher(test, topic_1);
  setup_one_publisher(test, topic_2);
  pid_t pid_topic2 = publisher_pid;

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = pid_topic2};
  int ret = get_filtered_publisher_num(topic_1, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, 1);
}

void test_case_get_filtered_publisher_num_with_exit(struct kunit * test)
{
  char * topic_name = "/kunit_test_ext_pub_exit";
  setup_one_publisher(test, topic_name);
  pid_t target_pid = publisher_pid;

  process_exit_cleanup(target_pid);

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = 0};
  int ret = get_filtered_publisher_num(topic_name, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, 0);
}

void test_case_get_filtered_publisher_num_no_publisher(struct kunit * test)
{
  char * topic_name = "/kunit_test_ext_pub_none";
  setup_one_subscriber(test, topic_name);

  union ioctl_get_filtered_publisher_num_args args = {.exclude_pid = 0};
  int ret = get_filtered_publisher_num(topic_name, current->nsproxy->ipc_ns, &args);

  KUNIT_EXPECT_EQ(test, ret, 0);
  KUNIT_EXPECT_EQ(test, args.ret_ext_publisher_num, 0);
}
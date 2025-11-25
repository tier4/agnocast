#include "agnocast_kunit_remove_subscriber.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

static char * node_name = "/kunit_remove_sub_node";
static uint32_t qos_depth = 10;
static bool qos_is_transient_local = false;
static bool is_take_sub = false;
static pid_t pid_cnt = 6000;

void test_case_remove_subscriber_normal(struct kunit * test)
{
  char * topic_name = "/kunit_remove_sub_normal";
  pid_t pid = pid_cnt++;

  union ioctl_add_process_args proc_args;
  add_process(pid, current->nsproxy->ipc_ns, &proc_args);

  union ioctl_add_subscriber_args sub_args;
  int ret_add = add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, pid, qos_depth, qos_is_transient_local,
    is_take_sub, &sub_args);

  KUNIT_ASSERT_EQ(test, ret_add, 0);

  topic_local_id_t target_id = sub_args.ret_id;

  union ioctl_get_subscriber_num_args num_args;
  get_subscriber_num(topic_name, current->nsproxy->ipc_ns, &num_args);
  KUNIT_EXPECT_EQ(test, num_args.ret_subscriber_num, 1);

  int ret_remove = remove_subscriber(topic_name, current->nsproxy->ipc_ns, target_id);
  KUNIT_EXPECT_EQ(test, ret_remove, 0);

  get_subscriber_num(topic_name, current->nsproxy->ipc_ns, &num_args);
  KUNIT_EXPECT_EQ(test, num_args.ret_subscriber_num, 0);
}

void test_case_remove_subscriber_invalid_id(struct kunit * test)
{
  char * topic_name = "/kunit_remove_sub_invalid_id";
  pid_t pid = pid_cnt++;

  add_process(pid, current->nsproxy->ipc_ns, &(union ioctl_add_process_args){});
  union ioctl_add_subscriber_args sub_args;
  add_subscriber(
    topic_name, current->nsproxy->ipc_ns, node_name, pid, qos_depth, qos_is_transient_local,
    is_take_sub, &sub_args);

  topic_local_id_t real_id = sub_args.ret_id;
  topic_local_id_t fake_id = real_id + 999;

  int ret = remove_subscriber(topic_name, current->nsproxy->ipc_ns, fake_id);
  KUNIT_EXPECT_EQ(test, ret, -ENODATA);

  union ioctl_get_subscriber_num_args num_args;
  get_subscriber_num(topic_name, current->nsproxy->ipc_ns, &num_args);
  KUNIT_EXPECT_EQ(test, num_args.ret_subscriber_num, 1);
}

void test_case_remove_subscriber_invalid_topic(struct kunit * test)
{
  char * topic_name = "/kunit_remove_sub_no_topic";

  int ret = remove_subscriber(topic_name, current->nsproxy->ipc_ns, 0);
  KUNIT_EXPECT_EQ(test, ret, -EINVAL);
}
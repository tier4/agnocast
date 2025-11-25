#include "agnocast_kunit_remove_publisher.h"

#include "../agnocast.h"
#include "../agnocast_memory_allocator.h"

static char * node_name = "/kunit_remove_pub_node";
static uint32_t qos_depth = 10;
static bool qos_is_transient_local = false;
static pid_t pid_cnt = 7000;

void test_case_remove_publisher_normal(struct kunit * test)
{
  char * topic_name = "/kunit_remove_pub_normal";
  pid_t pid = pid_cnt++;

  add_process(pid, current->nsproxy->ipc_ns, &(union ioctl_add_process_args){});

  union ioctl_add_publisher_args pub_args;
  int ret_add = add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, pid, qos_depth, qos_is_transient_local,
    &pub_args);

  KUNIT_ASSERT_EQ(test, ret_add, 0);
  topic_local_id_t target_id = pub_args.ret_id;

  int ret_remove = remove_publisher(topic_name, current->nsproxy->ipc_ns, target_id);
  KUNIT_EXPECT_EQ(test, ret_remove, 0);

  int ret_again = remove_publisher(topic_name, current->nsproxy->ipc_ns, target_id);
  KUNIT_EXPECT_EQ(test, ret_again, -ENODATA);
}

void test_case_remove_publisher_with_msg(struct kunit * test)
{
  char * topic_name = "/kunit_remove_pub_with_msg";
  pid_t pid = pid_cnt++;

  add_process(pid, current->nsproxy->ipc_ns, &(union ioctl_add_process_args){});

  union ioctl_add_publisher_args pub_args;
  add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, pid, qos_depth, qos_is_transient_local,
    &pub_args);
  topic_local_id_t pub_id = pub_args.ret_id;

  int ret = remove_publisher(topic_name, current->nsproxy->ipc_ns, pub_id);
  KUNIT_EXPECT_EQ(test, ret, 0);
}

void test_case_remove_publisher_invalid_id(struct kunit * test)
{
  char * topic_name = "/kunit_remove_pub_invalid_id";
  pid_t pid = pid_cnt++;

  add_process(pid, current->nsproxy->ipc_ns, &(union ioctl_add_process_args){});
  union ioctl_add_publisher_args pub_args;
  add_publisher(
    topic_name, current->nsproxy->ipc_ns, node_name, pid, qos_depth, qos_is_transient_local,
    &pub_args);

  topic_local_id_t fake_id = pub_args.ret_id + 100;

  int ret = remove_publisher(topic_name, current->nsproxy->ipc_ns, fake_id);
  KUNIT_EXPECT_EQ(test, ret, -ENODATA);
}